#!/usr/bin/env python3
# -*-:python; coding:utf-8; -*-
# author: Louis Abel <label@resf.org>
# RepoView3 is a utility to generate HTML pages for dnf
# repository, to make it easily browsable.
#
# This repoview has been rewritten to:
#
#     * Work with current dnf implementations
#     * Use jinja2 templating
#     * No reimplementation of RSS
#       * https://git.resf.org/sig_core/toolkit/src/branch/devel/mangle/generators/rss.py
#     * Make it stateless (for now?) (no sqlite)
#     * Support only what's in yum.repos.d (for now)
#
# Current original can be found here:
#
# https://github.com/sergiomb2/repoview
#
# TODO:
#   * Setup a table of checksums?
#   * Add support for group package type (e.g. mandatory)
#   * Make better looking pages
#   * Add support for remote locations

"""
RepoView3 is a utility that generates HTML pages for dnf repositories in order
to provide a browseable and viewable representation of a given repository.
Loosely based on the original yum implementation, this uses dnf-native modules
in order to gather and generate the right data.

It is named RepoView3 to note that is a rewrite in python3 and may be missing
features.

@author: Louis Abel <label@resf.org>
@license: GPLv2
"""

# pylint: disable=unused-import
import os
import shutil
import sys
import time
import datetime
import base64
from hashlib import sha256 as shahex
from functools import cmp_to_key
import argparse
# pylint can't find this. it's fine to ignore.
# pylint: disable=no-name-in-module
from rpm import labelCompare as lc
import dnf
from jinja2 import Environment as j2env, FileSystemLoader as j2fsl

VERSION          = '0.1.0'
TEMPLATE_PKG     = 'package.html.j2'
TEMPLATE_GRP     = 'group.html.j2'
TEMPLATE_INDEX   = 'index.html.j2'
FILE_PKG         = '%s.html'
FILE_GRP         = '%s.group.html'
FILE_INDEX       = 'index.html'
FORMAT           = "%a, %d %b %Y %X GMT"
ON_PAGE_FORMAT   = "%Y-%m-%d"

DEF_TEMPLATE_DIR = '/usr/share/repoview3/templates'

def to_unicode(string: str) -> str:
    """
    Convert to unicode
    """
    if isinstance(string, bytes):
        return string.decode('utf8')
    if isinstance(string, str):
        return string
    return str(string)

def to_base64(string: str) -> str:
    """
    Converts a string to base64, but we put single quotes around it. This makes
    it easier to regex the value.
    """
    string_bytes = string.encode('utf-8')
    string_conv = base64.b64encode(string_bytes)
    base64_str = "'" + string_conv.decode('utf-8') + "'"
    return str(base64_str)

def from_base64(string: str) -> str:
    """
    Takes a base64 value and returns a string. We also strip off any single
    quotes that can happen.
    """
    stripped = string.replace("'", "")
    conv_bytes = stripped.encode('utf-8')
    convd_bytes = base64.b64decode(conv_bytes)
    decoded = convd_bytes.decode('utf-8')
    return decoded

def human_size(numbytes: int):
    """
    Returns the size in units that makes sense (KiB or MiB).
    """
    if numbytes < 1024:
        return f'{numbytes} Bytes'
    kilos = numbytes/1024
    if kilos/1024 < 1:
        return f'{kilos} KiB'
    floater = float(kilos)/1024
    return f'{floater} MiB'

def unique_first_chara(lst: list) -> list:
    """
    Returns a sorted unique list of the first characters of each list item
    """
    uniques = list(set(pk[0] for pk in lst))
    uniques.sort()
    return uniques

def stamper(stamp):
    """
    Returns a simple date or timestamp string
    """
    return stamp.strftime(ON_PAGE_FORMAT)

def timer(stamp):
    """
    Returns a simple date or timestamp string
    """
    return time.strftime(ON_PAGE_FORMAT, time.localtime(int(stamp)))

def ezname(text):
    """
    Make a web friendly name out of whatever text is thrown here
    """
    text = text.replace('/', '.')
    text = text.replace(' ', '_')
    return text

def uniqlist(lst):
    """
    Takes a list and makes items unique
    """
    new_list = list(dict.fromkeys(lst))
    new_list.sort()
    return new_list

class DnfQuiet(dnf.Base):
    """
    DNF object
    """
    def __init__(self):
        dnf.Base.__init__(self)

    def substitute(self):
        """
        Applies all vars from /etc/dnf/vars
        """
        self.conf.substitutions.update_from_etc('/')

    def read_repos(self):
        """
        Gets all dnf repos from the system
        """
        self.read_all_repos()

    def get_data(self):
        """
        Gets all dnf data as requested
        """
        self.fill_sack()

    def get_group_objs(self):
        """
        Return all groups in the form of a list
        """
        available_groups = self.comps.groups
        return available_groups

    def get_groups(self):
        """
        Return all groups in the form of a list
        """
        groups = []
        available_groups = self.comps.groups
        for group in available_groups:
            groups.append(group.name)
        return groups

    def get_environments(self):
        """
        Return all environments in the form of a list
        """
        envs = []
        available_envs = self.comps.environments
        for env in available_envs:
            envs.append(env.name)
        return envs

    def get_recent(self, days=1):
        """
        Return most recent packages from dnf sack
        """
        recent = []
        now = time.time()
        recentlimit = now-(days*86400)
        ftimehash = {}
        if self.conf.showdupesfromrepos:
            available = self.sack.query().available().filter()
        else:
            available = self.sack.query().available().filter(latest_per_arch=1)

        available.run()

        for package in available:
            ftime = int(package.buildtime)
            if ftime > recentlimit:
                if ftime not in ftimehash:
                    ftimehash[ftime] = [package]
                else:
                    ftimehash[ftime].append(package)

        for sometime in ftimehash.keys():
            for package in ftimehash[sometime]:
                recent.append(package)

        return recent

# pylint: disable=too-many-instance-attributes
class RepoView:
    """
    Does the actual repoview stuff
    """
    # pylint: disable=too-many-statements
    def __init__(self, options):
        """
        Initialize the RepoView class
        """
        self.quiet   = options.quiet
        self.outdir  = options.output_dir
        self.link    = options.link
        self.title   = options.title
        self.desc    = options.description
        self.arches  = options.arches
        self.repoids = options.repoids
        self.tmpldir = options.template_dir

        # dnf things
        self.tempcache       = options.tempcache
        self.module_hotfixes = options.module_hotfixes
        self.disable_modules = options.disable_all_modules
        self.dnf_config      = options.config
        self.recents         = options.recents

        # template things
        self.j2loader = j2fsl(options.template_dir)
        self.j2env    = j2env(autoescape=True, trim_blocks=True, loader=self.j2loader)
        self.j2env.filters['stamper'] = stamper
        self.j2env.filters['timer'] = timer
        self.group_template = self.j2env.get_template(TEMPLATE_GRP)
        self.package_template = self.j2env.get_template(TEMPLATE_PKG)
        self.index_template = self.j2env.get_template(TEMPLATE_INDEX)

        # Actually do dnf stuff right here
        dnfobj = DnfQuiet()
        self.sout('Loading dnf')
        if options.config:
            self.sout('Loading config')
            dnfobj.conf.read(filename=options.config)

        if os.geteuid() != 0 or options.tempcache:
            cachedir = dnfobj.conf.cachedir
            if cachedir is None:
                self.serr('Error: Could not make cachedir')
                sys.exit(50)
            dnfobj.conf.cachedir = cachedir

        try:
            dnfobj.read_all_repos()
        except:
            self.serr('Could not read repos')
            sys.exit(1)

        if len(self.repoids) > 0:
            for repo in dnfobj.repos:
                repoobj = dnfobj.repos[repo]
                if repo not in self.repoids:
                    repoobj.disable()
                else:
                    repoobj.enable()
                    if options.module_hotfixes:
                        try:
                            repoobj.set_or_append_opt_value('module_hotfixes', '1')
                        except:
                            self.serr('Warning: dnf library is too old to support setting values')

                    repoobj.load_metadata_other = True

        self.sout('Getting all repo metadata')
        try:
            dnfobj.get_data()
        except:
            self.serr('repo data failure')
            sys.exit(1)

        if self.disable_modules:
            modobj = dnf.module.module_base.ModuleBase(dnfobj)
            modobj.disable(['*'])

        # data things
        self.sout('Obtaining group information')
        groups = dnfobj.get_group_objs()
        self.groups = self.get_group_data(groups)
        self.sout('Obtaining environment information')
        self.environments = dnfobj.get_environments()

        self.setup_output()

        # package things
        self.sout('Obtaining all package information')
        self.sack_query = dnfobj.sack.query().available()
        all_pkgs = self.sack_query.filter()
        self.sout('Sorting packages by name')
        self.named_pkgs = sorted(set(all_pkgs), key=lambda pkg: pkg.name)
        self.sout('Sorting packages by build time')
        sorted_pkgs = sorted(set(all_pkgs), key=lambda pkg: pkg.buildtime)
        sorted_pkgs.reverse()
        self.sout('Getting unique first character list')
        package_names = list(set(pkg.name for pkg in sorted_pkgs))
        letters = unique_first_chara(package_names)
        self.sout('Getting letter group package lists')
        self.letter_groups = self.get_letter_group_data(letters)
        self.sout(f'Getting {self.recents} of the latest packages')
        self.latest = self.proc_latest(sorted_pkgs[:self.recents])

        self.repo_filler = {
                'title': self.title,
                'letters': letters,
                'version': VERSION,
                'latest': self.latest
        }

        self.sout('Beginning to process data')
        self.proc_groups()

        self.sout('Writing index')
        output_file = os.path.join(self.outdir, 'index.html')
        with open(output_file, "w+") as of:
            of.write(self.index_template.render(
                repo_data=self.repo_filler,
                url=self.link,
                latest=self.latest,
                groups=self.groups,
                time=time.strftime(ON_PAGE_FORMAT)
            ))
            of.close()

    def proc_groups(self):
        """
        Process group data
        """
        self.sout('Processing group data')
        counter = 0
        for group_filler in self.groups + self.letter_groups:
            (group_name, group_description, group_file, pkg_list) = group_filler

            group_filler = {
                    'name': group_name,
                    'description': group_description,
                    'filename': group_file
            }

            packages = self.proc_packages(
                    self.repo_filler,
                    group_filler,
                    sorted(pkg_list)
            )

            group_filler['packages'] = packages

            # empty groups are ignored
            if not packages:
                self.sout(f"Group {group_filler['name']} is empty")
                del self.groups[counter]
                continue

            counter += 1
            self.sout(f'Writing group {group_filler["name"]}')
            output_file = os.path.join(self.outdir, group_filler['filename'])
            with open(output_file, "w+") as of:
                of.write(self.group_template.render(
                    repo_data=self.repo_filler,
                    group_data=group_filler
                ))
                of.close()


    def proc_packages(self, repo_data, group_data, pkg_list):
        """
        Process package data
        """
        pkgtups = []
        written = {}

        for pkg in pkg_list:
            pkg_file = ezname(FILE_PKG % pkg)
            if pkg in written.keys():
                pkgtups.append(written[pkg])
                continue

            pkg_data = self.get_package_data(pkg)

            # This shouldn't happen, but sometimes groups in comps
            # are just inaccurate.
            if pkg_data is None:
                continue

            pkgtup = (pkg, pkg_file, pkg_data['summary'])
            pkgtups.append(pkgtup)
            self.sout(f'Writing package {pkg} to {pkg_file}')
            self.package_template.group_data = group_data
            self.package_template.pkg_data = pkg_data
            output_file = os.path.join(self.outdir, pkg_file)
            with open(output_file, "w+") as of:
                of.write(self.package_template.render(
                    repo_data=repo_data,
                    group_data=group_data,
                    pkg_data=pkg_data
                 ))
                of.close()

            written[pkg] = pkgtup
        return pkgtups

    def proc_latest(self, pkglist):
        """
        Process the list of latest packages and return a list of tuples
        """
        tuplist = []
        for pkg in pkglist:
            filename = ezname(FILE_PKG % pkg.name)
            tuplist.append((pkg.name, filename, pkg.version, pkg.release, pkg.buildtime))

        return tuplist

    # pylint: disable=too-many-locals
    def get_package_data(self, name):
        """
        Returns a dict of package information
        """
        pkg_query = self.sack_query.filter(name=name)
        # we only want data from the first finding, in the case of
        # multi-version or multilib. but we also have to account for multiple
        if len(pkg_query) == 1:
            pkg_info = self._pkg_return(pkg_query[0])
            versions = [pkg_info]
        else:
            # for loop against the pkg_query and get the data
            # make sure that we only care about evra.
            # later we'll compare against evr for version ordering
            # epoch must be str for comparison purposes.
            tempcheck = {}
            versions = []
            for vers in pkg_query:
                tempcheck[(str(vers.epoch), vers.version, vers.release, vers.arch)] = vers

            keys = list(tempcheck.keys())
            keys.sort(
                    key=cmp_to_key(lambda a, b: lc(a[:3], b[:3])),
                    reverse=True
            )
            for key in keys:
                versions.append(self._pkg_return(tempcheck[key]))

        pkg_file = ezname(FILE_PKG % name)
        pkg_data = {
                'name':         name,
                'filename':     pkg_file,
                'summary':      None,
                'description':  None,
                'url':          None,
                'license':      None,
                'sourcerpm':    None,
                'vendor':       None,
                'rpms':         []
        }

        for data in versions:
            (name, epoch, version, release, arch, summary, description, url,
             buildtime, rpmlicense, sourcerpm, size, location, remote_location,
             vendor, changelogs, filelist) = data
            # we have to check this because if we have multiple
            # versions/packages we want to make sure we don't keep adding data
            # that's already there
            if pkg_data['summary'] is None:
                pkg_data['summary'] = summary
                pkg_data['description'] = description
                pkg_data['url'] = url
                pkg_data['license'] = rpmlicense
                pkg_data['sourcerpm'] = sourcerpm
                pkg_data['vendor'] = vendor

            size = human_size(size)

            # changelog stuff
            if changelogs is not None:
                changelog_list = changelogs.copy()
            else:
                changelog_list = []
            for meta in changelog_list[:2]:
                author = meta['author']
                try:
                    author = author[:author.index('<')].strip()
                except ValueError:
                    pass
                meta['author'] = author
                meta['text'].replace("\n", "<br />\n")

            pkg_data['rpms'].append((
                    epoch,
                    version,
                    release,
                    arch,
                    buildtime,
                    size,
                    location,
                    remote_location,
                    changelog_list,
                    filelist
            ))

        return pkg_data

    def get_group_data(self, groups):
        """
        Returns a tuple of group information
        """
        list_of_list = []
        pkg_list = []
        for group in groups:
            all_group_pkgs = (group.default_packages
                            + group.mandatory_packages
                            + group.optional_packages
                            + group.conditional_packages)
            if not group.visible or not all_group_pkgs:
                continue
            for pkg in all_group_pkgs:
                pkg_list.append(pkg.name)
            group_filename = ezname(FILE_GRP % group.id)
            list_of_list.append([group.ui_name,
                                 group.ui_description,
                                 group_filename,
                                 pkg_list])

        return list_of_list

    def get_letter_group_data(self, letters):
        """
        Returns data on packages part of a letter group
        """
        list_of_list = []
        for group in letters:
            pkggroup = f'Letter {group}'
            description = f'Packages beginning with the letter "{group}"'
            filtered = self.sack_query.filter(name__glob=f'{group}*')
            pkgs = []
            for filt in filtered:
                pkgs.append(filt.name)

            # There is a chance that a package may be multi-lib or may have
            # multiple versions of itself in a repo
            uniqpkgs = uniqlist(pkgs)
            group_filename = ezname(FILE_GRP % group)
            list_of_list.append([pkggroup,
                                 description,
                                 group_filename,
                                 uniqpkgs])

        return list_of_list

    def setup_output(self):
        """
        Setup the output directory
        """
        if os.access(self.outdir, os.R_OK):
            shutil.rmtree(self.outdir)
        else:
            os.mkdir(self.outdir, 0o755)

        # Layouts can be created - This is a carry over from the former repoview
        self.sout('Checking if we have a layout to copy')
        layout_src  = os.path.join(self.tmpldir, 'layout')
        layout_dest = os.path.join(self.outdir, 'layout')
        if os.path.isdir(layout_src) and not os.access(layout_dest, os.R_OK):
            self.sout('Copying layout')
            shutil.copytree(layout_src, layout_dest)

    def sout(self, msg):
        """
        Send a message to stdout
        """
        if not self.quiet:
            sys.stdout.write(msg + '\n')

    def serr(self, msg):
        """
        Send a message to stderr. Pierces quiet mode.
        """
        sys.stderr.write(msg + '\n')

    @staticmethod
    def _pkg_return(data):
        """
        Returns a tuple of needed package data. This func is to avoid
        duplicating the work in proc packages
        """
        ordered_data = (
                data.name,
                str(data.epoch),
                data.version,
                data.release,
                data.arch,
                data.summary,
                data.description,
                data.url,
                data.buildtime,
                data.license,
                data.sourcerpm,
                data.size,
                data.location,
                data.remote_location(),
                data.vendor,
                data.changelogs,
                data.files
        )
        return ordered_data

def main(options):
    """
    Start up the repoview script
    """
    RepoView(options)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--link', type=str, default='https://github.com/rpm-software-management/dnf',
                        help='URL link to repository root')
    parser.add_argument('--title', type=str, default='Repository Packages',
                        help='Title of the page')
    parser.add_argument('--description', type=str,
                        default='Package, group, and general repository information',
                        help='Description of the feed')
    parser.add_argument('--quiet', action='store_true',
                        help='Prevents messages on stdout and stderr.')

    dnf_opts = parser.add_argument_group("dnf options")
    dnf_opts.add_argument('--tempcache', action='store_true',
                        help='Temporary cache location (automatically on if not root)')
    dnf_opts.add_argument('--module-hotfixes', action='store_true',
                        help='Use this to catch all module packages alongside everything else')
    dnf_opts.add_argument('--arches', action='append', default=[],
                        help='List of architectures to care about')
    dnf_opts.add_argument('--config', type=str, default='',
                        help='A dnf configuration to use if you do not want to use the default')
    dnf_opts.add_argument('--disable-all-modules', action='store_true',
                        help='Disables all modules. Useful for getting newer than 8 data.')
    dnf_opts.add_argument('--recents', type=int, default=30, help='Number of latest packages')
    dnf_opts.add_argument('repoids', metavar='N', type=str, nargs='+')
    template_opts = parser.add_argument_group('template options')
    template_opts.add_argument('--output-dir', type=str, default='repoview')
    template_opts.add_argument('--template-dir', type=str,
                               default=DEF_TEMPLATE_DIR)
    results = parser.parse_args()

    main(results)

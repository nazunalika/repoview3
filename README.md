# repoview3

A python 3 rewrite of repoview using builtin dnf modules and functions.

This script is stateless, meaning there is no sqlite databases used nor is the
repo data of a repository accessed directly to obtain information. This should
work on any system that has `dnf` available, such as CentOS Stream, any
Enterprise Linux derivative, or Fedora Linux.

## Requirements

* dnf
* rpm
* python 3 (3.9 and above tested)

## Examples

```
python3 repoview3.py --template-dir $PWD/templates --output-dir /var/tmp/baseos/ --title "Rocky Linux 9 BaseOS" baseos
```

```
python3 repoview3.py --template-dir $PWD/templates --output-dir /var/tmp/f41/ --title "Fedora Linux 41" fedora
```

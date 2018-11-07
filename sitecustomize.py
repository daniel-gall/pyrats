"""
PyRats sitecustomize.py logs the dependencies of your users' python scripts for system planning purposes.  Descended from furius.ca's estimable snakefood.

PyRats will rat your users out to you.

PyRats is also snakefood.

PyRats also fly the jolly roger.
"""
import sys, logging, re
import logging.handlers
import os
from os.path import *
from operator import itemgetter
import ast
from ast import NodeVisitor
from ast import Delete, Num, Str, Name, List, Tuple
from ast import Assign

from collections import defaultdict

global_cache = {}
def cached_listdir(path):
    res = global_cache.get(path)
    if res is None:
        res = os.listdir(path)
        global_cache[path] = res
    return res

ERROR_IMPORT = "    Line %d: Could not import module '%s'"
ERROR_SYMBOL = "    Line %d: Symbol is not a module: '%s'"
ERROR_UNUSED = "    Line %d: Ignored unused import: '%s'"
ERROR_SOURCE = "       %s"
WARNING_OPTIONAL = "    Line %d: Pragma suppressing import '%s'"

def find_dependencies(fn, verbose, process_pragmas,
                      ignore_unused=False,
                      warning_lambda=logging.warning,
                      debug_lambda=logging.debug):
    "Returns a list of the files 'fn' depends on."
    file_errors = []
    try:
      this_ast, _ = parse_python_source(fn)
    except:
      return [], file_errors
    if this_ast is None:
        return [], file_errors
    found_imports = get_ast_imports(this_ast)
    if found_imports is None:
        return [], file_errors

    # Filter out the unused imports if requested.
    if ignore_unused:
        found_imports, unused_imports = filter_unused_imports(this_ast, found_imports)
        for modname, rname, lname, lineno, level, pragma in unused_imports:
            file_errors.append((ERROR_UNUSED, lname))

    files = []
    assert not isdir(fn)
    dn = dirname(fn)
    seenset = set()
    for x in found_imports:
        mod, rname, lname, lineno, level, pragma = x
        if process_pragmas and pragma == 'OPTIONAL':
            continue

        sig = (mod, rname)
        if sig in seenset:
            continue
        seenset.add(sig)
        if mod is None:
            continue
        modfile, errors = find_dotted_module(mod, rname, dn, level)

        if modfile is None:
            continue
        files.append(realpath(modfile))

    return files, file_errors

def find_imports(fn, verbose, ignores):
    "Yields a list of the module names the file 'fn' depends on."

    this_ast, _ = parse_python_source(fn)
    if this_ast is None:
        raise StopIteration

    found_imports = get_ast_imports(this_ast)
    if found_imports is None:
        raise StopIteration

    dn = dirname(fn)

    packroot = None
    for modname, rname, lname, lineno, _, _ in found_imports:
        islocal = False
        names = modname.split('.')
        if find_dotted(names, dn):
            # This is a local import, we need to find the root in order to
            # compute the absolute module name.
            if packroot is None:
                packroot = find_package_root(fn, ignores)
                if not packroot:
                    continue

            reldir = dirname(fn)[len(packroot)+1:]

            modname = '%s.%s' % (reldir.replace(os.sep, '.'), modname)
            islocal = True

        if rname is not None:
            modname = '%s.%s' % (modname, rname)
        yield (modname, lineno, islocal)

class ImportVisitor(ast.NodeVisitor):
    """AST visitor for grabbing the import statements.

    This visitor produces a list of

       (module-name, remote-name, local-name, line-no, pragma)

    * remote-name is the name off the symbol in the imported module.
    * local-name is the name of the object given in the importing module.
    """
    def __init__(self):
        self.modules = []
        self.recent = []

    def visit_Import(self, node):
        self.accept_imports()
        self.recent.extend(
                           (x.name, None, x.asname or x.name, node.lineno, 0)
                           for x in node.names)

    def visit_ImportFrom(self, node):
        self.accept_imports()
        modname = node.module
        if modname == '__future__':
            return # Ignore these.
        for x in node.names:
            name = x.name
            as_ = x.asname
            if name == '*':
                # We really don't know...
                mod = (modname, None, None, node.lineno, node.level)
            else:
                mod = (modname, name, as_ or name, node.lineno, node.level)
            self.recent.append(mod)

    # For package initialization files, try to fetch the __all__ list, which
    # implies an implicit import if the package is being imported via
    # from-import; from the documentation:
    #
    #  The import statement uses the following convention: if a package's
    #  __init__.py code defines a list named __all__, it is taken to be the list
    #  of module names that should be imported when from package import * is
    #  encountered. It is up to the package author to keep this list up-to-date
    #  when a new version of the package is released. Package authors may also
    #  decide not to support it, if they don't see a use for importing * from
    #  their package.
    def visitAssign(self, node):
        lhs = node.nodes
        if (len(lhs) == 1 and
            isinstance(lhs[0], AssName) and
            lhs[0].name == '__all__' and
            lhs[0].flags == OP_ASSIGN):

            rhs = node.expr
            if isinstance(rhs, (List, Tuple)):
                for namenode in rhs:
                    # Note: maybe we should handle the case of non-consts.
                    if isinstance(namenode, Num):
                        modname = namenode.value
                        mod = (modname, None, modname, node.lineno, 0)#node.level
                        self.recent.append(mod)
                    if isinstance(namenode, Str):
                        modname = namenode.value
                        mod = (modname, None, modname, node.lineno, 0)#node.level
                        self.recent.append(mod)
                    #if isinstance(namenode, Bytes):
                    #    modname = namenode.value
                    #    mod = (modname, None, modname, node.lineno, 0)#node.level
                    #    self.recent.append(mod)

    def default(self, node):
        pragma = None
        if self.recent:
            if isinstance(node, Discard):
                children = node.getChildren()
                if len(children) == 1 and isinstance(children[0], Num):
                    num_node = children[0]
                    pragma = num_node.value
                if len(children) == 1 and isinstance(children[0], Str):
                    str_node = children[0]
                    pragma = str_node.value
                #if len(children) == 1 and isinstance(children[0], Bytes):
                #    bytes_node = children[0]
                #    pragma = bytes_node.value

        self.accept_imports(pragma)

    def accept_imports(self, pragma=None):
        self.modules.extend((m, r, l, n, lvl, pragma)
                            for (m, r, l, n, lvl) in self.recent)
        self.recent = []

    def finalize(self):
        self.accept_imports()
        return self.modules

def check_duplicate_imports(found_imports):
    """
    Heuristically check for duplicate imports, and return two lists:
    a list of the unique imports and a list of the duplicates.
    """
    uniq, dups = [], []
    simp = set()
    for x in found_imports:
        modname, rname, lname, lineno, _, pragma = x
        if rname is not None:
            key = modname + '.' + rname
        else:
            key = modname
        if key in simp:
            dups.append(x)
        else:
            uniq.append(x)
            simp.add(key)
    return uniq, dups

def get_local_names(found_imports):
    """
    Convert the results of running the ImportVisitor into a simple list of local
    names.
    """
    return [(lname, no)
            for modname, rname, lname, no, _, pragma in found_imports
            if lname is not None]

class ImportWalker(NodeVisitor):
    "AST walker that we use to dispatch to a default method on the visitor."

    def __init__(self, visitor):
        NodeVisitor.__init__(self)
        self._visitor = visitor

    def default(self, node, *args):
        self._visitor.default(node)
        NodeVisitor.default(self, node, *args)

def parse_python_source(fn):
    """Parse the file 'fn' and return two things:

    1. The AST tree.
    2. A list of lines of the source line (typically used for verbose error
       messages).

    If the file has a syntax error in it, the first argument will be None.
    """
    # Read the file's contents to return it.
    # Note: we make sure to use universal newlines.
    try:
        #f = open(fn, 'r', encoding="utf-8")
        f = open(fn, 'r')
        contents = f.read()
        f.close()
        lines = contents.splitlines()
        line0_m = re.match('^[ \t\v]*#.*?coding[:=][ \t]*([-_.a-zA-Z0-9]+)', lines[0])
        line1_m = re.match('^[ \t\v]*#.*?coding[:=][ \t]*([-_.a-zA-Z0-9]+)', lines[1])
        if line0_m:
            f = open(fn, 'rU', encoding=line0_m.group(0))
            contents = f.read()
            f.close()
        elif line1_m:
            f = open(fn, 'rU', encoding=line1_m.group(0))
            contents = f.read()
            f.close()
        lines = contents.splitlines()
    except (IOError, OSError) as e:
        return None, None

    # Convert the file to an AST.
    try:
        this_ast = ast.parse(contents)
    except SyntaxError as e:
        return None, lines
    except TypeError as e:
        return None, lines

    return this_ast, lines

def get_ast_imports(this_ast):
    """
    Given an AST, return a list of module tuples for the imports found, in the
    form:
        (modname, remote-name, local-name, lineno, pragma)
    """
    assert this_ast is not None
    vis = ImportVisitor()
    vis.visit(this_ast)
    found_imports = vis.finalize()
    return found_imports


libpath = join(sys.prefix, 'lib', 'python%d.%d' % sys.version_info[:2])


exceptions = ('os.path',)
builtin_module_names = sys.builtin_module_names + exceptions

module_cache = {}

def find_dotted_module(modname, rname, parentdir, level):
    """
    A version of find_module that supports dotted module names (packages).  This
    function returns the filename of the module if found, otherwise returns
    None.

    If 'rname' is not None, it first attempts to import 'modname.rname', and if it
    fails, it must therefore not be a module, so we look up 'modname' and return
    that instead.

    'parentdir' is the directory of the file that attempts to do the import.  We
    attempt to do a local import there first.

    'level' is the level of a relative import (i.e. the number of leading dots).
    If 0, the import is absolute.
    """
    # Check for builtins.
    if modname in builtin_module_names:
        return join(libpath, modname), None

    errors = []
    names = modname.split('.')
    for i in range(level - 1):
        parentdir = dirname(parentdir)
    # Try relative import, then global imports.
    fn = find_dotted(names, parentdir)
    if not fn:
        try:
            fn = module_cache[modname]
        except KeyError:
            fn = find_dotted(names)
            module_cache[modname] = fn
    if fn:
        # If this is a from-form, try the target symbol as a module.
        if rname:
            fn2 = find_dotted([rname], dirname(fn))
            if fn2:
                fn = fn2
            else:
                errors.append((ERROR_SYMBOL, '.'.join((modname, rname))))
                # Pass-thru and return the filename of the parent, which was found.

    return fn, errors

try:
    from imp import ImpImporter
except ImportError:
    try:
        from pkgutil import ImpImporter
    except ImportError:
        #from snakefood.fallback.pkgutil import ImpImporter
        pass

def find_dotted(names, parentdir=None):
    """
    Dotted import.  'names' is a list of path components, 'parentdir' is the
    parent directory.
    """
    filename = None
    for name in names:
        mod = ImpImporter(parentdir).find_module(name)
        if not mod:
            break
        filename = mod.get_filename()
        if not filename:
            break
        parentdir = dirname(filename)
    else:
        return filename

def find_roots(list_dirofn, ignores):
    """
    Given a list of directories or filenames, find Python files and calculate
    the entire list of roots.
    """
    inroots = set()
    for fn in map(realpath, list_dirofn):

        # Search up the directory tree for a root.
        root = find_package_root(fn, ignores)
        if root:
            inroots.add(root)
        elif isfile(fn):
            inroots.add(dirname(fn))
        else:
            assert isdir(fn)

            # If the given file is not sitting within a root, search below the
            # directory tree for available roots.
            downroots = search_for_roots(fn, ignores)
            if downroots:
                inroots.update(downroots)
            else:
                logging.warning("Directory '%s' does live or include any roots." % fn)
    return sorted(inroots)

def find_package_root(fn, ignores):
    "Search up the directory tree for a package root."
    if not isdir(fn):
        fn = dirname(fn)
    while is_package_dir(fn):
        assert fn
        fn = dirname(fn)
    if fn and is_package_root(fn, ignores):
        return fn

def search_for_roots(dn, ignores):
    """Search below the directory tree for package roots.  The recursive search
    does not move inside the package root when one is found."""
    if not isdir(dn):
        dn = dirname(dn)
    roots = []
    for root, dirs, files in os.walk(dn):
        for d in list(dirs):
            if d in ignores:
                dirs.remove(d)
        if is_package_root(root, ignores):
            roots.append(root)
            dirs[:] = []
    return roots

def is_package_dir(dn):
    """Return true if this is a directory within a package."""
    return exists(join(dn, '__init__.py'))

def is_package_root(dn, ignores):
    """Return true if this is a package root.  A package root is a directory
    that could be used as a PYTHONPATH entry."""

    if not exists(dn) or exists(join(dn, '__init__.py')):
        return False

    else:
        dirfiles = (join(dn, x) for x in cached_listdir(dn))
        subdirs, files = filter_separate(isdir, dirfiles)

        # Check if the directory contains Python files.
        pyfiles = []
        for x in files:
            bx = basename(x)
            if bx in ignores:
                continue
            if bx.endswith('.so') or is_python(x):
                pyfiles.append(bx)

        # Note: we need to check for a 'site-packages' subdirectory because some
        # distributions package arch-specific files in a different place and
        # have no .py files in /usr/lib/pythonVER, but a single 'config' or
        # 'site-packages' directory instead. These aren't packages either.
        if join(dn, 'site-packages') in subdirs:
            return True

        # Check if the directory contains Python packages.
        for sub in subdirs:
            bsub = basename(sub)
            # Note: Make use of the fact that dotted directory names cannot be
            # imported as packages for culling away branches by removing those
            # subdirectories that have dots in them.
            if '.' in bsub or bsub in ignores:
                continue
            if exists(join(sub, '__init__.py')):
                return True

    return False

def relfile(fn, ignores):
    "Return pairs of (package root, relative filename)."
    root = find_package_root(realpath(fn), ignores)
    if root is None:
        root = dirname(fn)
        rlen = basename(fn)
    else:
        rlen = fn[len(root)+1:]

    assert root is not None and rlen is not None
    return root, rlen

def filter_separate(pred, seq):
    """Generic filter function that produces two lists, one for which the
    predicate is true, and the other elements."""
    inlist = []
    outlist = []
    for e in seq:
        if pred(e):
            inlist.append(e)
        else:
            outlist.append(e)
    return inlist, outlist

def output_depends(depdict, log_target, log_facility):
    """Given a dictionary of (from -> list of targets), generate an appropriate
    output file."""
    # Output the dependencies.
    #write = sys.stdout.write
    extra_logging_fields = {'python':sys.executable,}
    logger = logging.getLogger("PyRats")
    logger.propagate = False
    logger.setLevel(logging.INFO)
    import socket
    handler = logging.handlers.SysLogHandler(address=log_target, facility=logging.handlers.SysLogHandler.LOG_USER, socktype=socket.SOCK_DGRAM)
    formatter = logging.Formatter('Python: ts=%(asctime)s;loggerName=%(name)s;pathName=%(pathname)s;python=%(python)s;logRecordCreationTime=%(created)f;levelNo=%(levelno)s;levelName=%(levelname)s;message=%(message)s')

    handler.formatter = formatter
    logger.addHandler(handler)
    logger = logging.LoggerAdapter(logger, extra_logging_fields)
    PY3 = sys.version_info[0] == 3
    if  PY3:
        things = sorted(iter(depdict.items()), key=itemgetter(0))
    else:
        things = sorted(depdict.iteritems(), key=itemgetter(0))
    for (from_root, from_), targets in things:
        filtered_targets = []
        for thing1, thing2 in targets:
          #if thing1 is not None and thing2 is not None:
          if thing1 is not None:
            filtered_targets.append((thing1,thing2))
        if (len(filtered_targets)>=1):
            message_tokens = []
            for to_root, to_ in sorted(filtered_targets):
                message_tokens.append(repr( ((from_root, from_), (to_root, to_)) ))
            message = '),('.join(message_tokens)
            message = '(' + message + ')'
            if len(message) < 65220:
                try:
                    logger.info(message)
                except:
                    pass
                #write(repr( ((from_root, from_), (to_root, to_)) ))
                #write('\n')

def is_python(fn):
    "Return true if the file is a Python file."
    if fn.endswith('.py'):
        return True
    else:
        try:
            f = open(fn,'r')
            file_head = f.read(64)
            f.close()
            if re.match("#!.*\\bpython", file_head):
                return True
        except IOError:
            return False
        except:
            return False


def_ignores = ['.svn', 'CVS', 'build', '.hg', '.git']

def iter_pyfiles(dirsorfns, ignores, abspaths=False):
    """Yield all the files ending with .py recursively.  'dirsorfns' is a list
    of filenames or directories.  If 'abspaths' is true, we assumethe paths are
    absolute paths."""
    assert isinstance(dirsorfns, (list, tuple))
    assert isinstance(ignores, (type(None), list))

    ignores = ignores or def_ignores
    for dn in dirsorfns:
        if not abspaths:
            dn = realpath(dn)

        if not exists(dn):
            continue

        if not isdir(dn):
            if is_python(dn):
                yield dn

        else:
            for root, dirs, files in os.walk(dn):
                for r in ignores:
                    try:
                        dirs.remove(r)
                    except ValueError:
                        pass

                afiles = [join(root, x) for x in files]
                for fn in filter(is_python, afiles):
                    yield fn

def gendeps(log_target, log_facility):
    sys_dirs = []
    script_filename = sys.argv[0]
    args = [sys.argv[0],]

    class stub_opts:
      def __init__(self):
          self.ignores = []
          self.do_pragmas = True
          self.ignore_unused = False
          self.follow = True
          self.verbose = 0
    opts = stub_opts()
    fn = realpath(script_filename)
    inroots = find_roots(args, opts.ignores)
    sys.path = inroots + sys.path
    inroots = frozenset(inroots)

    allfiles = defaultdict(set)
    allerrors = []
    processed_files = set()
    fiter = iter_pyfiles(args, opts.ignores, False)
    while 1:
        newfiles = set()
        for fn in fiter:
            if fn in processed_files:
                continue # Make sure we process each file only once.

            processed_files.add(fn)

            # When packages are the source of dependencies, remove the __init__
            # file.  This is important because the targets also do not include the
            # __init__ (i.e. when "from <package> import <subpackage>" is seen).
            if basename(fn) == '__init__.py':
                fn = dirname(fn)

            if is_python(fn):
                files, errors = find_dependencies(
                    fn, opts.verbose, opts.do_pragmas, opts.ignore_unused)
                allerrors.extend(errors)
            else:
                # If the file is not a source file, we don't know how to get the
                # dependencies of that (without importing, which we want to
                # avoid).
                files = []
            # Make sure all the files at least appear in the output, even if it has
            # no dependency.
            from_ = relfile(fn, opts.ignores)
            if from_ is None:
                continue
            infrom = from_[0] in inroots
            allfiles[from_].add((None, None))
            # Add the dependencies.
            for dfn in files:
                xfn = dfn
                if basename(xfn) == '__init__.py':
                    xfn = dirname(xfn)
                if basename(dirname(xfn)).startswith("python"):
                    continue
                to_ = relfile(xfn, opts.ignores)
                into = to_[0] in inroots
                allfiles[from_].add(to_)
                newfiles.add(dfn)
        if not (opts.follow and newfiles) or len(newfiles)==0:
            break
        else:
            fiter = iter(sorted(newfiles))

    found_roots = set()
    try:
        for key, files in allfiles.iteritems():
            found_roots.add(key[0])
            found_roots.update(map(itemgetter(0),files))
    except:
        pass
    if None in found_roots:
        found_roots.remove(None)
    output_depends(allfiles, log_target, log_facility)

def pyrats():

    if len(sys.argv) >= 1:
        if (len(sys.argv[0])>0):
            if sys.argv[0][0] != '-':
                save_path = sys.path
                try:
                    gendeps(('your_log_server_fqdn',515), 20)
                except:
                    pass
                sys.path = save_path

class SetTrap(object):
  def __del__(self):
    pyrats()

if hasattr(sys,'argv') and sys.argv is not None:
    pyrats()
else:
    sys.argv = SetTrap()

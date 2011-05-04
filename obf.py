#!/usr/bin/env python

# obf.py:  A python-based parser for Open Behavioral [data] Format (OBF).
# Copyright 2011 by Jeremy R. Gray, jrgray@gmail.com
# Distributed under the terms of the GNU General Public License (GPL), v3.

# Note that OBF is a separate logical entity from code that implements a 
# parser or emitter; see OBF_spec.txt


__version__ = '0.4.00' # of the parser, not OBF

import yaml
import copy
import re
import time # just for code profiling


# Parser constants:
# Special section keys, case-sensitive:
_HEADER = '=Header='
_SESSION = '=Session='
_SUBJECT = '=Subject='
_PARTICIPANT = '=Participant='
_COMMENT = '=Comment='
_NOTES = '=Notes='
_FOOTER = '=Footer='
_SPECIAL = [_HEADER, _SESSION, _SUBJECT, _PARTICIPANT, _COMMENT, _NOTES, _FOOTER]

# Parser directives, not case-sensitive:
_STRICT = 'strict' # disallow (generate error, nullify data)
_WARN = 'warn' # permissive (generate a warning)
_NOT_STRICT = 'not_strict' # permissive, and quiet
_KEYS_LOWER = 'keys_lower' # convert keys to all upper-case
_KEYS_UPPER = 'keys_upper' # convert keys to all lower-case
_ONE_INDEXED = 'one_indexed' # first list element is [1], default
_ZERO_INDEXED = 'zero_indexed' # first list element is [0]
_AUTO_INDEX = 'auto_index' # add integer labels to redundant keys
_PREPROC = [_STRICT, _WARN, _NOT_STRICT,
            _KEYS_LOWER, _KEYS_UPPER,
            _ONE_INDEXED, _ZERO_INDEXED, _AUTO_INDEX]
_PREPROC = map(lambda x: x.lower(), _PREPROC)

# Units, not case-sensitive:
_UNITS_LABEL = 'units'
_UNITS = ['ms', 'sec', 'utime', # time: milliseconds, seconds, unix-time (sec)
               'cm',  # distance: centimeters
               'deg', # degrees (eg, visual angle)
               'hz',  # Hertz
               'pix', # pixels (e.g., image or screen dimensions)
               'norm', # norm units: -1 to +1 inclusive
               'rgb', 'dkl', 'lms', # color space
               'percent',  # 0 to 100 inclusive
               #'likert',  # Likert scale?
               'tf', 'yn', 'bool', # True-False, yes-no, boolean
               'hex', 'base64', # hexadecimal (base 16), base 64 (text encodings)
               #'utf8', # utf-8 (encoding)
               ]

# Regular expressions:
_valid_var_re = re.compile(r"^[a-zA-Z_][\w]*$")  # a string is a legal variable name
_bad_key_re = re.compile(r"[^a-z0-9.+, _]", re.I)  # non-OBF character (for a key)
_good_key_re = re.compile(r"^[a-z_][a-z0-9.+,\s_]*:\s+", re.I) # the line contains a good key
_almost_good_key_re = re.compile(r"^[a-z_][a-z0-9.+,\s_]*:[^\s]+", re.I) # lacks space after colon
_two_dots_re = re.compile(r".*\..*\.")  # two '.' anywhere
_looks_like_special_key_re = re.compile(r"^=.+=$")  # string is '=' first and last, with something in between
_label_dot_units_re = re.compile(r"^([a-zA-Z_][^.]*)\.(.+)$") # captures two groups, label, units
_numeric_re = re.compile(r"^\d+$")

class OBF_Load(dict):
    """Class for parsing a file-like data source consisting of OBF text.
    
    Parses text from a data source having a .readlines() method, using yaml.load()
    plus extra parsing specific to behavioral-data. Result:
    - self.data   <-- data structure
    - self.source <-- repr of data source
    - self.report <-- warning & error messages
    - self.time   <-- code timing profile
    - self.prepro <-- preprocessing requested
    - self.yaml   <-- yaml parser details
    
    Notes:
    - quote characters seem to mess with YAML parsing. to use '123' (string) 
      as a key for a dict (instead of as an integer), use _123_ -> ['123'] 
    
    Still needs:
    - better bad-key detection: get errors, but can be cryptic
    - standardize .report[] messages --> warn, quiet, strict
    - provide usage examples
    - provide tests
    
    Someday think about:
    - YAML does not require --- and ...; maybe good to check if they are in source
      likely useful for multiple data files per text source
    """
    
    # might be useful:
    # libyaml from http://pyyaml.org/wiki/LibYAML
    # I had build issues, no yaml.h, did not pursue; maybe this: http://pyyaml.org/ticket/70
    # interesting: yaml.load(input, Loader=yaml.CLoader)

    def __init__(self, source, conventions={}, timing=False, units=_UNITS):
        """
        """
        # initialize timing profile (generate one even if not requested)
        self.time = []
        self.time.append(('start',time.time()))
        self.time.append(('obf-load_start',time.time()))
        
        dict.__init__(self) # at first a dict made sense, but things have evolved
        self.source = str(source)  # save the name / repr of the source
        self.units = map(lambda x: x.lower(), units) # case-insensitive
        self.report = [] # container for warnings and other notes
        
        # details of the YAML parser used for this OBF parsing:
        self.yaml = {}
        self.yaml['__name__'] = yaml.__name__
        self.yaml['__version__'] = yaml.__version__
        try:
            self.yaml['__with_libyaml__'] = yaml.__with_libyaml__
        except AttributeError:
            self.yaml['__with_libyaml__'] = '(not applicable)'
        
        # read only once from the source:
        raw_text = source.readlines()
        
        # here could search for --- <stuff> ..., and split into multiple sources
        #yaml_opener = [i for i, line in enumerate(raw_text) if line.startswith('---')]
        #if len(yaml_opener) == 0:
        #    yaml_opener = [-1]
        #yaml_closer = [i for i, line in enumerate(raw_text) if line.startswith('...')]
        #if len(yaml_closer) == 0:
        #    yaml_closer = [len(raw_text)]
            
        # for multiple documents per file, refactor moving data{dict} to data[0]{dict}
        #self.data = [] but also self.report, self.source, ...
        # loop:
        #     text_chunk = raw_text[yaml_opener.pop(0)+1 : yaml_closer.pop(0)]
        #     self.data.append() = ..
        
        # look before leaping:
        self.initial_checks(raw_text)
        self.data, self.prepro = self.process_yaml(raw_text)
        
        # everything is 'key: value' pairs:
        self.parse_keys()
        
        # set conventions (hot_key: action pairings), then parse
        merged_conv = dict(_get_default_conventions(), **conventions) 
        self.process_values(merged_conv)
        
        # self.adjust_indices()  # if ONE_INDEXED alert about non-null [0] values?
        
        # reporting and strictness level:
        self.report = list(set(self.report))  # remove redundant
        if _STRICT in self.prepro:
            pass # if 'ERROR' in any message, nullify self.data
        if _NOT_STRICT in self.prepro:
            pass # remove 'ERROR' and 'WARNING' message from self.report
        
        if timing:
            # format the timing tuples:
            self.time.append(('obf-load_end',time.time()))
            self.time[1:len(self.time)] = ["%7.3f = %s" %(self.time[i][1] - self.time[0][1],
                                                self.time[i][0]) for i in range(1,len(self.time))]
            self.time.pop(0) # remove the initial reference point time-zero
        else:
            del self.time
            
    def __str__(self):
        return '<obf.OBF_Load() parsing of '+self.source+'>'
    def __repr__(self):
        return str(self)
    
    def initial_checks(self, raw_text):
        '''Perform some basic validations.
        '''
        # filter once:
        key_lines = [(i, line) for i, line in enumerate(raw_text) if not line[0] in [' ', '#', '-', '.']]
        special_lines = [line for i, line in key_lines if line.startswith('=')]
        
        header = [line for line in special_lines if line.startswith(_HEADER)]
        if len(header) != 1:
            raise AttributeError, "OBF: ERROR: must be one %s section" % _HEADER
        session = [line for line in special_lines if line.startswith(_SESSION)]
        if len(session) != 1:
            raise AttributeError, "OBF: ERROR: must be one %s section" % _SESSION
        subject = [line for line in special_lines if line.startswith(_SUBJECT) or line.startswith(_PARTICIPANT)]
        if len(subject) != 1:
            raise AttributeError, "OBF: ERROR: must be one %s or %s section" % (_SUBJECT, _PARTICIPANT)
        footer = [line for line in special_lines if line.startswith(_FOOTER) ]
        if len(footer) == 0:
            raise AttributeError, "OBF: WARNING: no %s section" % _FOOTER
        
        # avoid cryptic errors from YAML if colon-but-not-whitespace:
        colon_nonwhitespace = [i for i, line in key_lines if _almost_good_key_re.match(line)]
        for i in colon_nonwhitespace:
            key = raw_text[i][:raw_text[i].find(':')]
            self.report.append("OBF: WARNING: adding space after colon for key '%s'" % key)
            raw_text[i] = raw_text[i].replace(':', ': ')
        
    def process_yaml(self, raw_text):
        '''text wrangling
        find and apply preprocessing directives from =Header=
        parse as YAML using yaml.safe_load()
        '''
        # only need to work with lines having keys
        key_lines = [(i, line) for i, line in enumerate(raw_text) if _good_key_re.match(line)]
        
        # standardize / clean the text in keys:
        _clean_key_re = re.compile(r"^([a-z0-9_][a-z0-9.+, _]*[a-z0-9_])\s*:\s+", re.I)
        for i, line in key_lines:
            # easiest to just skip one character keys:
            if line.replace(' ','').find(':') == 1:
                continue 
            match = _clean_key_re.match(line) # capture the key, no trailing white space
            clean_key = match.group(1).replace(',', '+')
            clean_key = re.sub(r"\s*\+\s*",'+', clean_key)
            # replace the orig key with a cleaned-up version of itself:
            raw_text[i] = re.sub(r".*:", clean_key+':', raw_text[i]) 
        
        # do a first (and hopefully only) yaml conversion:
        text = '\n'.join(raw_text)
        self.time.append(('start yaml-load',time.time()))
        data0 = yaml.safe_load(text)
        self.time.append(('end yaml-load (with_libyaml = %s)' %
                            str(self.yaml['__with_libyaml__']), time.time()))
        
        prepro = []
        if 'preprocess' in data0[_HEADER].keys():
            prepro = data0[_HEADER]['preprocess']
            if prepro is None:
                prepro = []
            if type(prepro) == str:
                prepro = prepro.split(',')
            elif type(prepro) != list:
                self.report.append("OBF: 'preprocess: %s' not understood, so ignored" % str(prepro))
            prepro = map(lambda s: s.lower().strip().lstrip(), prepro)
            # check for unknown pre-proc
            if set(prepro).difference(_PREPROC):
                self.report.append("OBF: 'preprocess: %s' not understood, so ignored" %
                                   ', '.join(list(set(prepro).difference(_PREPROC))) )
            if _WARN in prepro:
                self.report.append("OBF: '%s' not implemented yet" % _WARN)
        
        # do pre-processing; must yaml.load() again if do auto_index:
        if len(prepro) > 0:
            obf_keys = set(data0.keys()).difference(set(_SPECIAL))
            key_lines = [(i, line) for i, line in enumerate(raw_text) if _good_key_re.match(line)]
            
            self.base_index = 1
            if _ZERO_INDEXED in prepro:
                self.base_index = 0
            if _AUTO_INDEX in prepro:
                # this does only the right-most loop; other loops are ambiguous
                for key in obf_keys:
                    matching_lines = [i for (i, line) in key_lines if line.find(key+':')==0]
                    if len(matching_lines) > 1:
                        # append increasing integers if more than one line
                        for k, linenum in enumerate(matching_lines):
                            raw_text[linenum] = raw_text[linenum].replace(key, key + '.' + str(k + self.base_index))
                # reload everything, now that lines have been disambiguated
                text = '\n'.join(raw_text)
                self.time.append(('start yaml-load #2 auto_index',time.time()))
                data0 = yaml.safe_load(text)
                self.time.append(('end yaml-load #2 auto_index',time.time()))
                obf_keys = set(data0.keys()).difference(set(_SPECIAL))
            if _KEYS_LOWER in prepro:
                for key in obf_keys:
                    if key != key.lower():
                        data0[key.lower()] = data0[key]
                        del data0[key]
            elif _KEYS_UPPER in prepro:
                for key in obf_keys:
                    if key != key.upper():
                        data0[key.upper()] = data0[key]
                        del data0[key]
        
        self.time.append(('end preprocess', time.time()))
        return data0, prepro
            
    def parse_keys(self):
        """
        inspect & process every key; expand valid keys as dimenions of self.data
        """
        t1 = time.time()
        # treat =key= as comments if not in special keys:
        nonspecial_keys = set(self.data.keys()).difference(set(_SPECIAL))
        ignore_keys = [k for k in nonspecial_keys if _looks_like_special_key_re.match(k)]
        for key in ignore_keys:
            self.report.append("OBF: ignoring key '%s'" % key)
            del self.data[key]
        
        # remove keys with illegal OBF characters:
        obf_keys = set(self.data.keys()).difference(set(_SPECIAL))
        bad_keys = [k for k in obf_keys if _bad_key_re.search(k)]
        for key in bad_keys:
            self.report.append("OBF: ignoring bad key '%s'" % key)
            del self.data[key]
        
        obf_keys = set(self.data.keys()).difference(set(_SPECIAL))
        simple_keys = [k for k in obf_keys if _valid_var_re.match(k)]
        other_keys = obf_keys.difference(set(simple_keys)) 
        
        # expand keys for nested loops (list or dict)
        self.pyc_cache = {} # command, .pyc
        self.name_cache = {} # name, bool
        for key in other_keys: # complex, simple.units
            name, index = key.split('.',1)
            # refactor: move units detection out of complex_key handling
            if index.lower() == _UNITS_LABEL:
                continue
            # some obf_keys with a '.' might be key.units, rather than trial.index:
            if index.lower() in self.units:
                if hasattr(self.data, name): 
                    self.report.append("OBF: ERROR: '%s' has units '%s', but key conflicts with existing key" % (key, index.lower()))
                else:
                    self.report.append("OBF: NOTE: treating '%s' as %s with units %s" % (key, name, index.lower()))
                    self.data[name] = copy.deepcopy(self.data[key])
                    self.data[name+'.'+_UNITS_LABEL] = index
                    del self.data[key]
                continue
            # parse each sub-item of the complex key: eg: name1.index1+name2.index2+...+nameN.indexN
            name_indices = [] # to contain (name, index) tuples
            for condition in key.split('+'):
                if condition.find('.') == -1:
                    self.report.append("OBF: ERROR: mal-formed complex key '%s'" % key)
                name, index = condition.split('.', 1)
                if _numeric_re.match(index):
                    name_indices.append((name, int(index), True))
                else:
                    name_indices.append((name, index, False))
            
            # "move" datum to its new place via copy, add, & delete orig:
            datum = copy.deepcopy(self.data[key])
            self._add_datum(name_indices, datum, key) # == the slow part
            del self.data[key]
        
        del self.pyc_cache
        del self.name_cache
        self.time.append(('end parse keys; time %.3f' % (time.time() - t1), time.time()))
    
    def _add_datum(self, name_indices, datum, key):
        '''
        Given a single data point, add it to self.data. The interesting part is to
        grow / expand self.data to accomodate the structure implied by the given
        (name, index, index_type_int) tuples, which indicate nested lists, dicts,
        or a combination. index_type_int is bool, to reduce "type(index)" checks.
        
        The request is to place a single data point in a multi-dimensional 
        space. Some of the dimensions may not exist at all yet, so they have
        to be created. The dimensions can be ordered (lists) or unordered (dicts),
        or a mixture. There is no constraint on the number of such dimensions.
        
        More detail: given a list of (name, index, index_type_int) tuples, convert it into a data 
        structure within self.data, accepting an aribtrary number of reference
        tuples (= dimensions). at each step, the type (list or dict) is inferred
        from the type of its index.
        
        Strategy: traverse the existing data structure starting from a known-good
        root, self.data, at each point check for the next dimension, where (name,
        index) are always pairs):
            self.data[n][i]
            self.data[n][i] [n][i]
            self.data[n][i] [n][i] ... [n][i] = datum
        
        Implementation: goes list-by-list building up a string (s_data_build_string)
        to instantiate non-existing but required lists / dicts. after the dimensions 
        are known to exist or newly created via exec(), finally exec() the build-string,
        assigning datum to it. This places a single value in the data structure.
        
        Implied items are created and set to None, namely list elements that have
        a lower index value that the current item but have not yet been set explicitly.
        These will either get filled in later with a subsequent datum, or will
        just remain None, indicating a missing value.
        
        Maybe there's a simpler way to do it, possibly after all items have been 
        parsed (rather than item by item on the fly, as done here).
        
        Used only by parse_keys()
        '''
        
        # might be useful: http://lucumr.pocoo.org/2011/2/1/exec-in-python/
        
        # to speed up exec, cache compiled bytecode in self.pyc_cache
        # also cache s_data_build_string (without compile) in self.pyc_cache
        # safer in separate cache? easier to debug?
        
        s_data_build_string = 'self.data'
        
        for name, index, index_type_int in name_indices:
            if index == 0 and self.base_index == 1:
                self.report.append("OBF: WARNING: '%s' requested, but index 0 received" % _ONE_INDEXED)
            
            s_data_build_string += "['"+name+"']"
            
            if s_data_build_string in self.name_cache: # then its existing already
                # make tmp be a reference to the currently end-most list or dict:
                cmd = 'tmp='+s_data_build_string
                if not cmd in self.pyc_cache:
                    self.pyc_cache[cmd] = compile(cmd, "<string>", "exec")
                exec(self.pyc_cache[cmd])
                
                # now assign to tmp to assign to self.data[][]...[][]:
                if index_type_int and type(tmp) == list:
                    # lengthen the list as needed:
                    while len(tmp) < index+1:
                        tmp.append(None)
                    if tmp[index] is None:
                        tmp[index] = {}
                elif not index_type_int and type(tmp) == dict:
                    # ensure that index is a key of name; init it if its a new key
                    if not index in tmp.keys():
                        tmp[index] = {}
                else: # mismatch was specifed in the data source
                    raise KeyError, "OBF: ERROR: fundamental ambiguity in '%s': conflicting key-types, key '%s'" % (self.source, key)
            else: # need a new list or dict
                self.name_cache[s_data_build_string] = True # set flag for next time
                if index_type_int:
                    # new empty list, of minimum required length (index):
                    cmd = s_data_build_string+'=[None for i in xrange('+str(index+1)+') ]'
                    if not cmd in self.pyc_cache:
                        self.pyc_cache[cmd] = compile(cmd, "<string>", "exec")
                    exec(self.pyc_cache[cmd])
                    
                    cmd = s_data_build_string+'['+str(index)+']={}' # always {}, will get next name
                    if not cmd in self.pyc_cache:
                        self.pyc_cache[cmd] = compile(cmd, "<string>", "exec")
                    exec(self.pyc_cache[cmd])
                else:
                    # new empty dict referenced by index as a key
                    cmd = s_data_build_string+'={"'+index+'": {}}'
                    if not cmd in self.pyc_cache:
                        self.pyc_cache[cmd] = compile(cmd, "<string>", "exec")
                    exec(self.pyc_cache[cmd])
            s_data_build_string += '['+repr(index)+']'
        
        exec(s_data_build_string+'='+repr(datum))
        
    def process_values(self, conventions):
        """Inspect and process every value, descending recursively.
        
        Keys can trigger further processing, based on conventions.
        """
        hot_keys = conventions.keys() # unordered
        def walk_values(this_level):
            """trigger actions based on hot_keys; "walk" means descend recursively.
            
            Conventions consist of hot_key: action pairs, and are not formally part
            of the OBF definition. Custom conventions can be defined and
            passed to OBF_Load, as conventions={hot_key: function_reference, ...}.
            
            hot_keys are regular expressions, and must either be constants or include
            the start ^ and end $ delimiters (i.e., must be constructed to match
            the entire string exactly). See _get_default_conventions().
            A re.match(hot_key_regex, this_key) triggers a function call. That call
            returns a dict indicating what was done.
            
            The idea is that one and only one match should be allowed. It would be more
            powerful to allow multiple matches; that would require also being able 
            to specify the order in which matches should be attempted.
            """
            if type(this_level) == list:
                for item in this_level: # or this_level[self.base-index:]?
                    if type(item) in [list, dict]:
                        walk_values(item)
            elif type(this_level) == dict:        
                for key in this_level.keys():
                    status = None
                    for regex in hot_keys:
                        if regex == key or (regex[0] == '^' and regex[-1] == '$' and re.match(regex, key)):
                            status = conventions[regex](this_level, key, self)
                            break
                    if status:
                        for k in status.keys():
                            # if k == some-code: do something
                            if k == 'new_key': key = status['new_key']
                    if type(this_level[key]) in [list, dict]:
                        walk_values(this_level[key])
            else:
                assert False, "OBF: BUG in walk_values(): received a '%s'" % type(this_level)
        walk_values(self.data)
        self.time.append(('end parse values', time.time()))

class OBF_Dump(object):
    """Class for creating an OBF file-like data source; OBF text -> internal data.
    
    """
    def __init__(self):
        pass
    def dump(self):
        """ might want to use "default_flow_style=False"
        >>> print yaml.dump(yaml.load(document), default_flow_style=False)
        a: 1
        b:
          c: 3
          d: 4
        """
        pass
    def write(self):
        pass
    def flush(self):
        pass
    def write_header(self):
        pass
    def write_session(self):
        pass
    def write_subject(self):
        pass
    
    
def _get_default_conventions():
    """Returns a dict of default 'hot keys' = key + actions to be triggered.
    
    UNRESOLVED: being a dict is unordered, and it might be useful to know
    the order in which items are tried. On the other hand, it might actually be good to
    disallow order, so that matches can (must) have one and only one possible
    interpretation. 
    
    This allows for extensions in terms of custom (key: function) dict entries.
    The default keys are only semi-reserved, because they can be over-ridden by
    passing a different binding to custom_actions, when calling load(source, custom_actions={} )
    
    Keys can be given as a literal string to match, or as a regular expression.
    If a regex, it must including a leading ^ and ending $ to match the entire string;
    Keys that lack both a leading ^ and ending $ are simply compared using ==. 
    
    def some_action(this_dict, this_key, this_obj):
    - this action was triggered by 'this_key' of 'this_dict' 
    - typically do something with the value, this_dict[key], not the key
    - can also update this_dict or this_obj (eg, this_obj.report -> self.report)
    - return ('flag', a_value)
    """
    def convert_digits_as_str(this_dict, this_key, this_obj):
        # convert '_123_' to '123', to allow digits as a str in dict keys
        new_key = this_key.replace('_', '') # leave as str, only digits
        this_dict[new_key] = copy.deepcopy(this_dict[this_key])
        del this_dict[this_key]
        return {'new_key': new_key}
    def process_units(this_dict, this_key, this_obj):
        # interpret name.label as a name with units of label
        match = _label_dot_units_re.match(this_key) # captures
        if match:
            new_key = match.group(1)
            units = match.group(2)
            if units.lower() == _UNITS_LABEL:
                return
            if units.lower() in this_obj.units:
                units = units.lower()
            this_dict[new_key] = copy.deepcopy(this_dict[this_key])
            this_dict[new_key+'.'+_UNITS_LABEL] = units
            del this_dict[this_key]
            return {'new_key': new_key}
        else:
            this_obj.report.append("OBF: WARN: bad units for '%s." % this_key)
    def screen_random_seed(this_dict, this_key, this_obj):
        if this_dict[this_key] == 'None':
            this_obj.report.append("OBF: WARNING: ambiguous random_seed 'None'")
    def screen_mouse(this_dict, this_key, this_obj):
        mouse = this_dict[this_key]
        if type(mouse) == dict:
            if not 'x' in mouse and not 'y' in mouse:
                if 'pos' in mouse and type(mouse['pos'])==list and len(mouse['pos'])==2:
                    return
                else:
                    this_obj.report.append("OBF: ERROR: mouse lacks (x,y) or pos[]")
    key_action_dict = {
        # regex 'trigger': function_reference,
        'random_seed': screen_random_seed,
        'mouse': screen_mouse,
        r"^_\d+_$": convert_digits_as_str,
        r"^[a-zA-Z_].*\..+$": process_units
        #'key': screen_key
        }
    return key_action_dict

# Example of a custom key:action dict, here will nullify all default actions:
def clear_default_actions():
    """Returns a custom key:action dict with all default keys having action == pass.
    
    If this dict is used as
        OBF_Load(source, custom_actions=obfp.clear_default_actions())
    it overrides the default key:actions, so the defaults are effectively ignored. 
    One could get this dict, and then add to it, and so construct a completely 
    custom key: action dict, without any of the usual defaults.
    """
    def _do_nothing(this_dict, this_key, this_obj):
        pass
    key_action_dict = {}
    for key in _get_default_conventions():
        key_action_dict[key] = _do_nothing
    return key_action_dict

def example1():
    return '''
=Header=:
    encoding: utf-8  # of this file
    default units: sec
    format: OBF v0.1    # merely informative
    
    preprocess:  one_indexed    # parser directives
    program: PsychoPy2  # program used to create the data file
    version: 1.64.00    # string
    
=Session=:
    experiment:
        name: my_script.py  # == the name of the script used to generate this data file
        authors:  # string or list of strings; empty (as it is here) will parse as 'None'
        sha1.hex: 044db3cbb2b27a09ce6bbb2a1d9988a5e4cc1571
            # sha1 (hex-encoded) digest of my_script.py
        script.base64:
            # a base64-encoded copy of my_script.py, stashed here in the data file
    session_start.utime: 1303844359.088219  # unix time = date + time
    date: 2011-04-26    # redundant but nice to have human-readable too
    time: 09:19.45.230
    computer: scan-mac03
    scanner:
        TR.sec: 2.000  # float
        scanner: MRRC timtrioa  # string
    random_seed: None

=Subject=:
    code: tr1234  # string; multiple subject codes are possible, [code1, code2]
    sex: male
    age: 23
    group: A
    consenter: XYZ # person administering informed consent
    tester: XYZ # person who administered the tasks, often same as consenter

welcome:
    stimulus: Welcome. In this study you will do some cool stuff and get paid.
    
consent:
    stimulus: Press 'y' to agree to participate.
    response:
        key: y
        
instructions:
    onset: 0.042
    duration: 6.221
    stimulus: The scanner will start in just a few seconds.

loop.1 + trial.1:
    onset: 12.321
    tag: press2
    stimulus: press 2
    response:
        key: 2
        correct: True
        RT: 0.654
    
loop.1 + ITI.1:
    onset: 13.321
    duration: 5.000
    
loop.1 + trial.2:
    onset: 18.321
    tag: press2
    stimulus: press 2
    response:
        key: 2
        correct: True
        RT: 0.654
    
loop.1 + ITI.2:
    onset: 23.321
    duration: 5.000
    
loop.2 + trial.0002:
    onset: 18.345
    tag: press2
    stimulus: press 2
    response:
        key: 3
        correct: False
        RT: 0.444
    
loop.2 + ITI.2:
    onset: 19.321
    duration: 3.000

loop.0: 1

debriefing:
    stimulus: How was that?
    response:
        # a list (-) of multi-line strings (|); indentation matters
        - | 
            it was kind of noisy in the scanner
            my back is a little sore
        - |
            it was cool to see
            my brain

# lists as data values:
multiple_mouse_clicks:
    onset: 122.43
    stimulus: click 5 times
    tag: multiple mouse
    mouse:
        click_on: release
        sample: clicks  # vs frames
        # 5 clicks => lists of length 5
        button: [left, left, middle, right, right]
        xx: [10, 20, 30, 40, 50]  
        y: [20, 30, 40, 50, 70]
        RT.ms: [543, 1033, 3449, 5467, 6587] # a list tagged with units
        wheel_rel: [0, 0, 0, 0, 0]
        
# Deeply nested loops & dicts are possible
# here is a single data point, value == 'vroom':
list_of_lists.0+b.0+c.0+d.0+e.0+f.0+g.0+h.0+i.0+j.0+k.0+l.0+m.0+n.0+o.0+p.0+q.0+r.0+s.0+t.0+u.0+v.0+w.0+x.0+y.0+z.0: vroom
# and again
dict_of_dicts.a+b.b+c.c+d.d+e.e+f.f+g.g+h.h+i.i+j.j+k.k+l.l+m.m+n.n+o.o+p.p+q.q+r.r+s.s+t.t+u.u+v.v+w.w+x.x+y.y+z.z: vroom

# more typical trial structure, several loops, multiple trials
trial.1 + text.red + color.blue:
    response: blue
    rt.ms: 765
trial.2 + text.red + color.blue:
    response: blue
    rt.ms: 765
#
#trial.999 + text.red + color.blue:
#    response: blue
#    rt.ms: 765

# note that items [0, 3-998] will be set to None -- their presence is implied by trial.999

zz10.9:8 # illegal YAML syntax, but warn and correct (add a space) 
zz10.units: ms

zzz._1_:
    1111

_1_:1


=Footer=:
    exit_status: normal
    session_end.utime: 1303998240.246597
'''

def test_OBF_Load():
    """Run tests.
    """
    import StringIO 
    
    data = OBF_Load(StringIO.StringIO(example1()))
    
    # test for expected parsing:
    assert 'zz10' in data.data.keys()
    assert len(data.data['list_of_lists']) == 1
    
    # test for expected error messages:
    assert "OBF: WARNING: adding space after colon for key 'zz10.9:8'" in data.report
    
    print 'all tests pass'
    
    
if __name__ == '__main__':
    import StringIO 
    import sys
    
    if len(sys.argv) > 1:
        source = open(sys.argv[1])
    else:
        source = StringIO.StringIO(example1())
    
    t0 = time.time()
    data = OBF_Load(source, timing=True)
    t1 = time.time() - t0
    
    #print data.data['zzz'] # test _1_ -> '1'
    #print data.time
    
    for k in sorted(data.data):
        print k, data.data[k]
    print data.report
    
    for t in data.time:
        print t
    
    
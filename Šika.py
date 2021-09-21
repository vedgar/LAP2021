import itertools, inspect, functools


@functools.cache
class TruthValue:
    Me, Md, Mn, no = '''tfab
                        ftba
                        abtf
                        baft'''.split(), '''tttt
                                            tftf
                                            ttaa
                                            tfab'''.split(), '''ftba''', 0
    def __init__(self, letter):
        self.letter = letter
        self.index = TruthValue.no
        TruthValue.no += 1

    def __repr__ (self): return self.letter
    def __index__(self): return self.index
    def __bool__ (self): return self.letter == 't'

    def __eq__(self, other): return TruthValue(self.Me[self][other])
    def __or__(self, other): return TruthValue(self.Md[self][other])
    def __invert__  (self ): return TruthValue(self.Mn[self]       )
    def __gt__(self, other): return self | other == other


class Validation:
    def Ae (x, y, z): return ((x == y) == z) == (x == (y == z))
    def Fe (x, y, z): return ((x == z) == (y == z)) == (x == y)
    def Se (x, y   ): return (x == y) == (y == x)
    def Re (x      ): return x == x
    def Ad (x, y, z): return x | (y | z) == (x | y) | z
    def Sd (x, y   ): return x | y == y | x
    def Id (x      ): return x | x == x
    def Dde(x, y, z): return x | (y == z) == (x | y == x | z)
    def Fd (x, y, z): return (y == z) > (x | y == x | z)
    def Dne(x, y   ): return (x == ~ y) == ~ (x == y)
    def n3 (x      ): return x | ~ x


Omega = [TruthValue(letter) for letter in 'tfab']

def check(property, name):
    print('checking', name)
    n_args = len(inspect.signature(property).parameters)
    for args in itertools.product(Omega, repeat=n_args):
        result = property(*args)
        if not result: print('\t', name, args, '==', result)

for name, property in vars(Validation).items():
    if not name.startswith('_'): check(property, name)

# CS 3020 Final Project

For our final project we attempted to implement strings, string concatenation, and string comparison into our compiler.

---

## Implementation

- Support for string constants in the parser.
- Support for string creation
  - Added a case in select instructions that turns a string constant into a tuple of the ascii codes for the string's characters
- Support for string printing
  - Added a match case to the print case in select instructions that uses print_str if given a string
  - Implemented print_str in runtime.c
- Concatenation
  - Added the 'concat' primitive operator
  - Added a 'concat' case to the typecheker, asserting that the types of the expressions are strings
  - Allocates a new string that can hold the concatenation of both strings
  - Copys characters from the two strings into the new string
  - Adds null terminator to the end of the string
  - Added 'strlen' and 'memcpy' to runtime.c
- Comparison
  - Edited case `cif.Assign(x, [atm1, atm2])` to handle string comparison. Checks if atm1 and atm2 are strings, then calls strcmp on them.
  - Added 'strcmp' to runtime.c

---

## Planned but **NOT** implemented features

- Originally wanted to implement floats as well, but realized strings were enough of a challenge.
- Other string comparisons, >, <, !=, >=, <=
- Concatenation of more than two strings

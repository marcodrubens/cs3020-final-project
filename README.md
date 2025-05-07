# String Support Implementation Notes

This document outlines the steps and implementation details for adding string constant and operation support to the compiler and runtime system.

---

## Parser Updates

- **Current Limitation**: No support for string constants in the parser.
- **Required Change**:  
  - In `cs3020-support/python_parser.py`, on **line 88**, modify the parser to recognize string constants.
  - Add `str` to the type assertion in the constant case:
    ```python
    assert isinstance(c, (bool, int, str))
    ```

---

## Compiler Changes

### Constant Handling

- Add support for **string creation** in the `select_instructions` pass.
- Transform string constants into tuples of ASCII codes:
  ```python
  ord("hi")  # becomes (104, 105)
  ```
- You can **copy/paste** the tuple construction case and apply `ord()` to each character.

---

### String Printing

- Modify the `"print"` case in `select_instructions` to handle strings.
  
**Options:**
1. Implement `print_str` in `runtime.c`.
2. Print each character’s ASCII code using the existing `print_int` function.

---

### Primitive Operation: `concat`

- Allocate a new string to hold the **concatenation** of both input strings.
- Implement this in `select_instructions`.
- Support in `runtime.c`:
  - Added `strlen` to measure string lengths.
  - Used `memcpy` to copy characters from each string.

---

### String Comparison: `==`

- Edited `select_instructions`:
  - In the case `cif.Assign(x, cif.Prim(op, [atm1, atm2]))`, detect when `atm1` and `atm2` are strings.
  - Use `strcmp` to compare them.
- Updates to `runtime.c`:
  - Included `string.h`.
  - Added function:
    ```c
    int strcmp(const char* s1, const char* s2);
    ```

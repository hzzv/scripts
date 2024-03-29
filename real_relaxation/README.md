The script `relax.py` transforms a SMT-LIB benchmark from NIA to NRA.
The script supports logics `QF_UFDTNIA`, `QF_UFNIA`, and `QF_NIA` in the input, and assumes that all multiplications have exactly two arguments.

The script requires Python3 and [pysmt](https://github.com/pysmt/pysmt).
You might need to install [pyenv](https://github.com/pyenv/pyenv#installation).
To set up the environment (you only need to do this once):
```
pipenv sync
```

To run the script:
```
pipenv run python3 relax.py --input_file nia.smt2 --output_file nra.smt2
```

Additional options:
- `--more_precise_frac` to use a version of the `axiom_frac_bound` using `1-1/y` (`-1-1/y`) as a upper (lower) bound for `ufrax(x, y)`
- `--no_relax_inequality` to turn off the inequality relaxation
- `--no_frac_zero` to avoid adding the `axiom_frac_zero` axiom
- `--no_int_approx` to avoid adding the `axiom_int_approximation` axiom
- `--uninterp_mod_simple` to use a simpler definition of `umod`: `umod(x, y) := if 0 <= x < y then x else y*ufrac(x, y)`
- `--uninterp_mod_simplest` to use the simplest definition of `umod`: `umod(x, y) := y*ufrac(x, y)`

For some input files containing deeply nested expressions or long assertions, you might need to increase the shell stack size (e.g. by `ulimit -S -s hard`).

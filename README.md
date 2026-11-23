# OEIS A192745 — proof of Mathar's recurrence

**Status:** Mathematical proof complete. The main recurrence has been Lean-verified in Colab; the polynomial-evaluation bridge is a **compilation candidate**, not yet kernel-verified; compile it in Lean 4 + Mathlib before claiming formal verification. An explicit `modByMonic` identity is not yet formalized.

## The conjecture

[OEIS A192745](https://oeis.org/A192745) is the coefficient of `X` after reducing the polynomial `P_n(X)` by `X² = X + 1`, where `P_0(X)=1` and `P_n(X)=X P_(n-1)(X)+n!` for `n>0`.

R. J. Mathar conjectured (May 4, 2014), for `n >= 3`:

    a(n) - n*a(n-1) + (n-2)*a(n-2) + (n-1)*a(n-3) = 0.

## Proof

Write `P_n(X) ≡ u_n + a_n X` modulo `X²-X-1`. Multiplying by `X` sends `(u,a)` to `(a,u+a)`. Thus

    u_(n+1) = a_n + (n+1)!,
    a_(n+1) = u_n + a_n.

Eliminating `u` gives, for `n >= 2`,

    a_n = a_(n-1) + a_(n-2) + (n-1)!.

At `n-1`, the same identity gives

    a_(n-1) = a_(n-2) + a_(n-3) + (n-2)!.

Subtract `(n-1)` times the second equation from the first, using `(n-1)!=(n-1)(n-2)!`, and rearrange:

    a_n - n*a_(n-1) + (n-2)*a_(n-2) + (n-1)*a_(n-3) = 0.

This establishes the conjecture for every `n >= 3`.

## Lean verification

From a Lean 4 / Mathlib project:

    lake env lean A192745.lean

Check that compilation exits with code 0 and `#print axioms` reports no `sorryAx`.

The source formalizes the coefficient-pair recurrence, factorial elimination, and a polynomial evaluation characterization. The canonical remainder equality via `Polynomial.modByMonic` is not included.

## Attribution and priority

- OEIS sequence author: Clark Kimberling (2011).
- Recurrence conjecture: R. J. Mathar (2014).
- Factorial–Fibonacci convolution formula: Greg Dresden (2021).
- Proof prepared November 23, 2026.

The homogenization technique is standard. In particular, Tong Niu's May 2026 paper on [A002627](https://arxiv.org/abs/2605.15500) explicitly describes the general method. The closely related [A392898](https://oeis.org/A392898) already records a factorial-forced Fibonacci recurrence and its homogenization. An earlier explicit proof for A192745 has not been conclusively excluded; do not claim discovery of the technique or worldwide priority.

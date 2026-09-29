-- Prove2me | Theorems.Thm_Polynomial_mem_range_of_unique_common_root
-- name    : Polynomial.mem_range_of_unique_common_root
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/059deab2-7e60-5275-95da-b2b308cb1ae6
-- title:
--   Unique common root of a split separable polynomial is rational
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra, and let $A, B \in F[X]$. Assume $A \neq 0$, that the image $A^{L}$ of $A$ under the coefficient map $F \to L$ splits over $L$ (`Polynomial.Splits` for a polynomial over a field, i.e. $A^{L}$ factors into linear factors in $L[X]$), and that the multiset of roots of $A^{L}$ has no repetitions, so that $A^{L}$ has only simple roots. Let $x \in L$ satisfy $A(x) = 0$ and $B(x) = 0$, where the evaluation is via the structure map $F \to L$, and suppose $x$ is the only common zero: every $y \in L$ with $A(y) = 0$ and $B(y) = 0$ equals $x$. Then $x$ lies in the range of `algebraMap F L`, i.e. $x$ is the image of an element of $F$. Note that $B$ is not assumed nonzero and no separability or normality hypothesis is imposed on the extension $L/F$ beyond the splitting and simplicity of the roots of $A$.
--
--   This is a descent criterion for a point of $L$ to be $F$-rational, obtained by looking at the greatest common divisor of $A$ and $B$ in $F[X]$, whose reduction over $L$ must be linear. It is used in the treatment of modular curves, for instance by [`ModularCurve.full_eq_adjoin_primes`](thm.html#ModularCurve.full_eq_adjoin_primes) and [`ModularCurve.full_sq_eq_adjoin`](thm.html#ModularCurve.full_sq_eq_adjoin), to show that certain coordinates cut out by a pair of polynomial relations already lie in the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_mem_range_of_unique_common_root.lean

import Mathlib.Algebra.Polynomial.Splits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Polynomial.mem_range_of_unique_common_root {F L : Type*} [Field F] [Field L] [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0) (hAs : (A.map (algebraMap F L)).Splits) (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0) (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) : x ∈ (algebraMap F L).range := by sorry

-- Prove2me | Theorems.Thm_QSVT19_Main_theorem_4_first_claim
-- name    : QSVT19.Main.theorem_4_first_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:27.887852+00:00
-- url     : https://prove2.me/theorems/75f30dfd-4d3a-4ea5-a418-1da0b6dc1db2
-- title:
--   Theorem 4 (first claim): which $P$ extend to a quantum signal processing pair
-- statement:
--   Let $k\in\mathbb N$ and $P\in\mathbb C[x]$. There is $Q\in\mathbb C[x]$ such that $P,Q$ form a QSP pair of degree $k$ (properties (i)–(iii) of Theorem 3) if and only if $\deg P\le k$, $P$ has parity $k\bmod 2$, and
--   1. (iv.a) $|P(x)|\le1$ for all $x\in[-1,1]$;
--   2. (iv.b) $|P(x)|\ge 1$ for all $x\in(-\infty,-1]\cup[1,\infty)$;
--   3. (iv.c) if $k$ is even, then for all $x\in\mathbb R$,
--   $$P(ix)\,P^*(ix)\ge 1.$$
--
--   These are exactly the requirements that Corollary 8 places on the target polynomial.
--
--   **Formalization Note** In (iv.c), "$\ge1$" for a complex number means real and at least $1$ (Mathlib's `ComplexOrder`). $P^*$ has the conjugated coefficients. The theorem's second claim, about $Q$, is not included.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 10, Theorem 4 (first claim, (iv.a)–(iv.c))

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 4 (first claim), p. 10: "Let k ∈ N be fixed. Let P ∈ C[x], there exists some
Q ∈ C[x] such that P, Q satisfy properties (i)-(iii) of Theorem 3 if and only if P satisfies
properties (i)-(ii) of Theorem 3 and
(iv.a) ∀x ∈ [−1, 1]: |P(x)| ≤ 1
(iv.b) ∀x ∈ (−∞, −1] ∪ [1, ∞): |P(x)| ≥ 1
(iv.c) if k is even, then ∀x ∈ R: P(ix)P^∗(ix) ≥ 1."

**Formalization Note.** Properties (i)–(iii) of Theorem 3 are `IsQSPPair k P Q`; (i)–(ii) for
`P` alone are `deg P ≤ k` and parity `k mod 2`. `P^*` is `P.map (starRingEnd ℂ)`. In (iv.c) the
comparison `1 ≤ z` of complex numbers is Mathlib's `ComplexOrder`: `z` is real and at least
`1`. The second claim of Theorem 4 ((v.a)–(v.b), about `Q`) is not part of this statement. -/
theorem theorem_4_first_claim (k : ℕ) (P : ℂ[X]) :
    (∃ Q : ℂ[X], IsQSPPair k P Q) ↔ ((P.degree ≤ k ∧ QAlgorithms.HasParity P k) ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) ∧ (∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x : ℂ)‖) ∧ (Even k → ∀ x : ℝ, (1 : ℂ) ≤ P.eval (Complex.I * x) * (P.map (starRingEnd ℂ)).eval (Complex.I * x))) := by sorry

end QSVT19.Main

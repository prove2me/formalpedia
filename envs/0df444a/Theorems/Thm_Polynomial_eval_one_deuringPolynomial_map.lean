-- Prove2me | Theorems.Thm_Polynomial_eval_one_deuringPolynomial_map
-- name    : Polynomial.eval_one_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/401bbaa1-676c-5475-93ef-974eed5df18b
-- title:
--   Value at 1 of the Deuring polynomial mod q
-- statement:
--   Let $F$ be a field and let $q$ be a natural number which is prime (as a `Fact` instance), and suppose $F$ has characteristic $q$. Write $m = (q-1)/2$, where both the subtraction and the division are the truncated operations on natural numbers, so that $m = (q-1)/2$ for odd $q$ and $m = 0$ for $q = 2$. The Deuring polynomial over $\mathbb{Z}$ is defined as the finite sum $$\mathrm{deuringPolynomial}\ q = \sum_{i=0}^{m} \binom{m}{i}^2 X^i \in \mathbb{Z}[X],$$ the index $i$ running over $\{0,\dots,m\}$ and the coefficients being the integer casts of the squared binomial coefficients. The assertion is that after applying the ring homomorphism $\mathbb{Z} \to F$ coefficientwise to obtain a polynomial in $F[X]$, its value at $1 \in F$ equals $(-1)^{m}$ in $F$; that is, $\sum_{i=0}^{m} \binom{m}{i}^2 \equiv (-1)^{(q-1)/2}$ in $F$.
--
--   This computes the value at the degenerate Legendre parameter $\lambda = 1$ of the Deuring (Hasse) polynomial whose roots are the supersingular $\lambda$-invariants in characteristic $q$; in particular the value is nonzero, so $\lambda = 1$ is never a root. It is used in the treatment of $\lambda$-invariants and widths on the modular curve, in [`ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial`](thm.html#ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial) and [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial), and in the construction of supersingular endomorphisms in [`WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic`](thm.html#WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eval_one_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.eval_one_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [Fact q.Prime]
    [CharP F q] : ((deuringPolynomial q).map (Int.castRingHom F)).eval 1 = (-1) ^ ((q - 1) / 2) := by sorry

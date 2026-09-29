-- Prove2me | Theorems.Thm_Polynomial_pow_mul_eval_inv_deuringPolynomial_map
-- name    : Polynomial.pow_mul_eval_inv_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/9e4961d6-c319-518e-846c-48c2a73f7059
-- title:
--   Self-reciprocity of the Deuring polynomial
-- statement:
--   Let $F$ be a field, let $q$ be a natural number, and write $m = (q-1)/2$ for the truncated subtraction and division in $\mathbb{N}$. The Deuring polynomial is the integral polynomial $\mathrm{deuringPolynomial}\;q = \sum_{i=0}^{m} \binom{m}{i}^{2} X^{i} \in \mathbb{Z}[X]$, the sum being over $i$ in $\{0,\dots,m\}$ with coefficients the squares of binomial coefficients, viewed in $F$ via the image of this polynomial under the ring homomorphism $\mathbb{Z} \to F$ applied coefficientwise. The assertion is that for every $t \in F$ with $t \neq 0$,
--   $$t^{m} \cdot \Big(\sum_{i=0}^{m} \binom{m}{i}^{2} t^{-i}\Big) = \sum_{i=0}^{m} \binom{m}{i}^{2} t^{i},$$
--   that is, $t^{m} H_q(t^{-1}) = H_q(t)$ where $H_q$ denotes the image of the Deuring polynomial in $F[X]$ and $H_q(\cdot)$ its evaluation. No hypothesis is imposed on $q$ beyond being a natural number, and none on the characteristic of $F$; in particular $q$ need not be prime.
--
--   This is the palindromic (self-reciprocal) symmetry of the Deuring polynomial, reflecting $\binom{m}{i} = \binom{m}{m-i}$; one consequence is that the set of nonzero roots of $H_q$ in $F$ is stable under $\alpha \mapsto \alpha^{-1}$. It is used in [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial), where the roots of $H_q$ in characteristic $q$ are grouped into orbits in the course of the Eichler–Deuring mass formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_pow_mul_eval_inv_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.pow_mul_eval_inv_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) (t : F)
    (ht : t ≠ 0) :
    t ^ ((q - 1) / 2) * ((deuringPolynomial q).map (Int.castRingHom F)).eval t⁻¹
      = ((deuringPolynomial q).map (Int.castRingHom F)).eval t := by sorry

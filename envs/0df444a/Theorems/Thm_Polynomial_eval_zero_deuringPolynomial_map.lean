-- Prove2me | Theorems.Thm_Polynomial_eval_zero_deuringPolynomial_map
-- name    : Polynomial.eval_zero_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5121504a-f0db-5554-9399-2a2cc3954269
-- title:
--   The Deuring polynomial has constant term 1
-- statement:
--   Let $F$ be a field and let $q$ be a natural number. Write $m = (q-1)/2$, computed with truncated subtraction and floor division on $\mathbb{N}$, and let $$H_q = \sum_{i=0}^{m} \binom{m}{i}^2 X^i \in \mathbb{Z}[X]$$ be the Deuring polynomial `deuringPolynomial q`, the sum over $i$ in the range $\{0,\dots,m\}$ of the constant $\binom{m}{i}^2$, viewed in $\mathbb{Z}$, times $X^i$. The theorem asserts that the image of $H_q$ in $F[X]$ under the coefficientwise map induced by the canonical ring homomorphism $\mathbb{Z} \to F$ takes the value $1$ at $X = 0$; that is, the constant term of $H_q$ is $\binom{m}{0}^2 = 1$, and its image in $F$ is the unit of $F$. No hypothesis is imposed on $q$ (in particular it need not be prime or odd) and none on $F$ beyond being a field; the characteristic of $F$ is arbitrary.
--
--   This records that $\lambda = 0$ is never a root of the reduction of the Deuring (Hasse) polynomial, whatever the field: the degenerate Legendre parameter $\lambda = 0$ does not occur among the supersingular parameters. It is used in the study of the supersingular parameters via the Deuring polynomial, for instance by [`ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial`](thm.html#ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial), [`ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow`](thm.html#ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow) and [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eval_zero_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.eval_zero_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) :
    ((deuringPolynomial q).map (Int.castRingHom F)).eval 0 = 1 := by sorry

-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one
-- name    : WeierstrassCurve.exists_valuation_eq_exp_of_not_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/f89d942c-8e85-5294-aa47-5d6adf511407
-- title:
--   Poles of order 2s and 3s on an integral Weierstrass model
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$; write $v$ for the valuation of $K$ attached to the height-one prime $\mathfrak m =$ `IsDiscreteValuationRing.maximalIdeal R`, normalised so that every element of (the image of) $R$ has $v \le 1$. Let $W$ be a Weierstrass curve over $K$ which is integral over $R$ in the sense of `WeierstrassCurve.IsIntegral`, so that each of the coefficients $a_1, a_2, a_3, a_4, a_6$ of $W$ is the image under `algebraMap R K` of the corresponding coefficient of an integral model over $R$. Let $x, y \in K$ satisfy the affine Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$, and assume that $v(x) \le 1$ fails, i.e. $x$ is not $\mathfrak m$-integral. Then there is a natural number $s$ with $s > 0$ such that $v(x) = \exp(2s)$ and $v(y) = \exp(3s)$ in $\mathbb{Z}_{m0}$; in additive notation, $x$ has a pole of order exactly $2s$ and $y$ a pole of order exactly $3s$ at $\mathfrak m$.
--
--   This is the standard description of affine points of a Weierstrass model with non-integral coordinates, as in the analysis of the kernel of reduction: the pole orders of $x$ and $y$ are in the ratio $2:3$. It is used in the present development by [`WeierstrassCurve.reducePoint_some_add_some_of_not_le_one`](thm.html#WeierstrassCurve.reducePoint_some_add_some_of_not_le_one), in establishing the behaviour of reduction on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_valuation_eq_exp_of_not_le_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x = WithZero.exp (2 * (s : ℤ)) ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y = WithZero.exp (3 * (s : ℤ)) := by sorry

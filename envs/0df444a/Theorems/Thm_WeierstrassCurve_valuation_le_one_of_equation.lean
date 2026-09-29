-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_le_one_of_equation
-- name    : WeierstrassCurve.valuation_le_one_of_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/7ace9a12-f21c-52f3-b4eb-00dc8d903bfb
-- title:
--   Integral x forces integral y on an integral Weierstrass model
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it a field of fractions of $R$. Let $W$ be a Weierstrass curve over $K$ which is integral over $R$ in the sense of the class `WeierstrassCurve.IsIntegral`, so that each of the coefficients $a_1, a_2, a_3, a_4, a_6$ of $W$ is the image in $K$ of an element of $R$. Write $v$ for the $K$-valuation `IsDedekindDomain.HeightOneSpectrum.valuation` attached to the maximal ideal of $R$, a multiplicatively written valuation for which $v(t) \le 1$ exactly when $t$ lies in $R$. Let $x, y \in K$ satisfy the affine Weierstrass equation of $W$, namely $y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$, and assume $v(x) \le 1$. Then $v(y) \le 1$.
--
--   This is the standard integrality statement for points on a Weierstrass equation with coefficients in a discrete valuation ring: a point whose $x$-coordinate is integral has integral $y$-coordinate, because $y$ is a root of a monic quadratic with integral coefficients. It is used in the analysis of the reduction map on points, where the kernel is identified with the points having non-integral $x$-coordinate; it is cited by [`WeierstrassCurve.reducePoint_add`](thm.html#WeierstrassCurve.reducePoint_add), [`WeierstrassCurve.reducePoint_some_add_some_of_le_one`](thm.html#WeierstrassCurve.reducePoint_some_add_some_of_le_one) and [`WeierstrassCurve.reducePoint_some_add_some_of_not_le_one`](thm.html#WeierstrassCurve.reducePoint_some_add_some_of_not_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_le_one_of_equation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.valuation_le_one_of_equation
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 := by sorry

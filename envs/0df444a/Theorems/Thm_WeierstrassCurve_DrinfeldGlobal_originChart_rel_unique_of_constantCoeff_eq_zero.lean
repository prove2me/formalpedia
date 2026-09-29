-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero
-- name    : WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/703f96d8-f74d-568f-9c96-651f9789821d
-- title:
--   Uniqueness of small solutions of the origin-chart Weierstrass relation
-- statement:
--   Fix a type $\sigma$ of variables and a commutative ring $R$, and work in the ring $\mathrm{MvPowerSeries}\ \sigma\ R$ of formal power series in the variables $\sigma$ over $R$. Let $a_1, a_2, a_3, a_4, a_6$, $x$, $v$ and $v'$ be such power series. Assume that $x$, $v$ and $v'$ all have vanishing constant coefficient, and that both $v$ and $v'$ satisfy the same relation with the same $x$ and the same coefficients, namely
--   $$v + a_1 x v + a_3 v^2 = x^3 + a_2 x^2 v + a_4 x v^2 + a_6 v^3$$
--   and
--   $$v' + a_1 x v' + a_3 v'^2 = x^3 + a_2 x^2 v' + a_4 x v'^2 + a_6 v'^3 .$$
--   Then $v = v'$. No hypothesis is imposed on the coefficients $a_1,\dots,a_6$, and the ring $R$ is an arbitrary commutative ring; the conclusion is an identity of power series, not merely a congruence modulo some power of the maximal ideal.
--
--   This is the uniqueness half of the solvability of the Weierstrass equation in the chart at the origin, in the coordinates $(x,v)$ in which the curve is given by $v + a_1xv + a_3v^2 = x^3 + a_2x^2v + a_4xv^2 + a_6v^3$, here for power series in an arbitrary set of variables rather than a single one. It is used in the construction of the origin section and the formal group law of a Weierstrass curve, being cited by [`WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_constantCoeff_eq_zero
    {σ : Type u} {R : Type u} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x v v' : MvPowerSeries σ R)
    (hx : MvPowerSeries.constantCoeff x = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    (hv' : MvPowerSeries.constantCoeff v' = 0)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by sorry

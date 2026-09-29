-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero
-- name    : PachDeZeeuw.Algebraic.planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:23.167559+00:00
-- url     : https://prove2.me/theorems/7adc9f84-0885-4c3c-bb63-2fd20c519502
-- title:
--   Zero-curry curve equals coefficient-line zero set of its constant term
-- statement:
--   Let $h$ be a bivariate real polynomial with $h_{deg0} : (\mathrm{Curry0}\,h).\mathrm{natDegree} = 0$, i.e. $h$ viewed as a univariate polynomial in the first variable (over the coefficient ring $\mathrm{XCoeff}$) is constant. Then its plane zero set is exactly the coefficient-line zero set of that constant coefficient:
--
--   $${\mathrm{PlaneCurveZeroSet}\,h = \mathrm{CoeffLineZeroSet}\,((\mathrm{Curry0}\,h).\mathrm{coeff}\,0).}$$
--
--   This characterizes degenerate (vertical) curves: a polynomial independent of the first variable cuts out a union of vertical lines $X_1 = x$ indexed by the roots of its coefficient. It is the structural lemma behind every zero-curry case split, reducing intersections involving such an $h$ to fiberwise univariate root counts.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1114-L1148

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0) :
    PlaneCurveZeroSet h = CoeffLineZeroSet ((Curry0 h).coeff 0) := by sorry

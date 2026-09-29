-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_curry_isPrimitive_of_irreducible_positive_natDegree
-- name    : PachDeZeeuw.Algebraic.curry_isPrimitive_of_irreducible_positive_natDegree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:25.316631+00:00
-- url     : https://prove2.me/theorems/4970bf55-d530-43c2-a506-555b541b3d2e
-- title:
--   Currying of an irreducible positive-degree plane polynomial is primitive
-- statement:
--   Let $h$ be an irreducible bivariate real polynomial ($\mathrm{Irreducible}\,h$) whose currying has positive degree, $0 < (\mathrm{Curry}_0(h)).\mathrm{natDegree}$. Then the curried univariate polynomial over the coefficient ring is primitive:
--
--   $$\mathrm{IsPrimitive}(\mathrm{Curry}_0(h)).$$
--
--   Primitivity (content a unit) is the hypothesis needed for Gauss-type arguments: it allows coprimality over the coefficient ring to be transported to the fraction field, where the resultant nonvanishing argument runs.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1086-L1096

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.curry_isPrimitive_of_irreducible_positive_natDegree (h : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h)
    (hpos : 0 < (Curry0 h).natDegree) :
    (Curry0 h).IsPrimitive := by sorry

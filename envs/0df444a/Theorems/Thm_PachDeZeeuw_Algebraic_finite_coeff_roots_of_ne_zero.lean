-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_finite_coeff_roots_of_ne_zero
-- name    : PachDeZeeuw.Algebraic.finite_coeff_roots_of_ne_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:39.344613+00:00
-- url     : https://prove2.me/theorems/3a27bc5c-8130-4951-8ef6-10a89cf2722e
-- title:
--   Finiteness of coefficient-polynomial roots
-- statement:
--   Let $r$ be a nonzero element of the coefficient ring $\mathrm{XCoeff}$ ($r \ne 0$). Then its real root set is finite:
--
--   $$\mathrm{Finite}(\mathrm{CoeffRootSet}(r)).$$
--
--   This is the univariate fact (a nonzero real polynomial has finitely many roots, transported across `XCoeffEquiv`) that makes every 'bad locus' argument work: resultants, leading coefficients, and discriminants each vanish at only finitely many coefficient values, so all but finitely many fibers are good.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L767-L798

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.finite_coeff_roots_of_ne_zero (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).Finite := by sorry

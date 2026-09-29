-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le
-- name    : PachDeZeeuw.Algebraic.totalDegree_pderiv_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:20.406351+00:00
-- url     : https://prove2.me/theorems/c62db665-0044-453b-a36f-358b42442445
-- title:
--   Partial derivative total degree bounded by that of $h$
-- statement:
--   Let $h$ be a bivariate real polynomial and $i : \mathrm{Fin}\,2$ a variable index. Then formal partial differentiation does not increase total degree:
--
--   $${(\mathrm{pderiv}\,i\,h).\mathrm{totalDegree} \leq h.\mathrm{totalDegree}.}$$
--
--   There are no further hypotheses. The proof splits on whether $h.\mathrm{totalDegree}$ is positive: if so, `totalDegree_pderiv_le_sub_one` gives the stronger bound $h.\mathrm{totalDegree} - 1$; otherwise $h$ is a constant, its partial derivative is $0$, and the bound is trivial. It is used in `factor_intersection_bound` and `finite_singularities_of_irreducible_bound` to bound the total degree of a normalized factor of $\partial_i h$ by the degree bound $d$ of $h$.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1390-L1401

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.totalDegree_pderiv_le (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree := by sorry

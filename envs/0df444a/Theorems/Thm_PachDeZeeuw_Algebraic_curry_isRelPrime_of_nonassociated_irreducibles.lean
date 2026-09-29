-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_curry_isRelPrime_of_nonassociated_irreducibles
-- name    : PachDeZeeuw.Algebraic.curry_isRelPrime_of_nonassociated_irreducibles
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:39.501834+00:00
-- url     : https://prove2.me/theorems/b7232916-5dba-414a-943b-ce6567f3ab02
-- title:
--   Currys of nonassociated irreducibles are relatively prime
-- statement:
--   Let $h$ and $k$ be irreducible bivariate real polynomials that are not associated ($\neg\,\mathrm{Associated}\,h\,k$, i.e. they do not differ by a unit factor). Then their currys are relatively prime as univariate polynomials over the coefficient ring:
--
--   $$\mathrm{IsRelPrime}(\mathrm{Curry}_0(h),\, \mathrm{Curry}_0(k)).$$
--
--   This converts the geometric hypothesis 'distinct irreducible curves' into the algebraic coprimality hypothesis required for the resultant to be nonzero, and hence for the pair-intersection bound.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1098-L1112

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.curry_isRelPrime_of_nonassociated_irreducibles (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k) :
    IsRelPrime (Curry0 h) (Curry0 k) := by sorry

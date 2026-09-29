-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_ncard_coeff_roots_le_totalDegree
-- name    : PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:01.465085+00:00
-- url     : https://prove2.me/theorems/7b9533ae-9f1f-4e29-8e00-c57382fbada6
-- title:
--   Root count of nonzero $r : \mathrm{XCoeff}$ bounded by $r.\mathrm{totalDegree$
-- statement:
--   Let $r$ be a nonzero univariate coefficient polynomial, $r : \mathrm{XCoeff} = \mathrm{MvPolynomial}\,(\mathrm{Fin}\,1)\,\mathbb{R}$ with hypothesis $h_r : r \neq 0$, and let $\mathrm{CoeffRootSet}\,r$ be its set of real roots. Then the number of distinct real roots is bounded by the total degree:
--
--   $${(\mathrm{CoeffRootSet}\,r).\mathrm{ncard} \leq r.\mathrm{totalDegree}.}$$
--
--   This is the univariate root bound in coefficient-ring form: a nonzero polynomial over the integral domain $\mathbb{R}$ has at most $\deg r$ roots. It is the key quantitative input that turns finiteness of coefficient-root sets (e.g. roots of resultants) into explicit numerical bounds feeding the fiber-counting and pair-intersection estimates.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L800-L838

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).ncard ≤ r.totalDegree := by sorry

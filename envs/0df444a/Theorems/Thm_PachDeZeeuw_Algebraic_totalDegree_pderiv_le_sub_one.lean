-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le_sub_one
-- name    : PachDeZeeuw.Algebraic.totalDegree_pderiv_le_sub_one
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:45.13756+00:00
-- url     : https://prove2.me/theorems/5a5ea63b-4fe7-4834-8918-3b0cbbdeebb5
-- title:
--   Positive-degree partial drops total degree by at least one
-- statement:
--   Let $h$ be a bivariate real polynomial, $i : \mathrm{Fin}\,2$ a variable index, and assume $h$ has positive total degree (binder `_hpos` $: 0 < h.\mathrm{totalDegree}$). Then the partial derivative has total degree at most one less:
--
--   $${(\mathrm{pderiv}\,i\,h).\mathrm{totalDegree} \leq h.\mathrm{totalDegree} - 1,}$$
--
--   with truncated natural-number subtraction. The positivity hypothesis appears in the statement but is not used by the proof, which works monomial by monomial: differentiating a monomial with exponent vector $v$ either kills it (if $v_i = 0$) or lowers the exponent sum by exactly one. The lemma is used in `totalDegree_pderiv_le` (the positive-degree branch) and in `totalDegree_pderiv_lt_of_nonzero`, which in turn supports `irreducible_not_dvd_nonzero_partial` in the singularity analysis.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1354-L1388

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.totalDegree_pderiv_le_sub_one (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2)
    (_hpos : 0 < h.totalDegree) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree - 1 := by sorry

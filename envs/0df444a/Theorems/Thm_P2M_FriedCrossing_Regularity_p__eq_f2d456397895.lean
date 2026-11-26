-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_p__eq_f2d456397895
-- name    : P2M_FriedCrossing_Regularity_p__eq_f2d456397895
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:53.945739+00:00
-- url     : https://prove2.me/theorems/eae95e62-d3d0-59eb-ada3-2f390f7e73bb
-- title:
--   P2 M Fried Crossing Regularity p  eq f2d456397895: P2 M Fried Crossing Regularity p  eq f2d456397895
-- statement:
--   The P2 M Fried Crossing Regularity p  eq f2d456397895 construction uses the P2 M Fried Crossing Regularity p  eq f2d456397895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L152-L154
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L152-L154

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_p__eq_f2d456397895 {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pτ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1) := by sorry

alias «FriedCrossing».«Regularity».«pτ_eq» := P2M_FriedCrossing_Regularity_p__eq_f2d456397895

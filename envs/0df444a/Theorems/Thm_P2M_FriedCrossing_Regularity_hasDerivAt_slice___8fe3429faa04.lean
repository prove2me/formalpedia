-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04
-- name    : P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:43.502103+00:00
-- url     : https://prove2.me/theorems/4f32d0fa-8c3f-5651-a4ff-2b24d231df13
-- title:
--   P2 M Fried Crossing Regularity has Deriv At slice   8fe3429faa04: P2 M Fried Crossing Regularity has Deriv At slice   8fe3429faa04
-- statement:
--   The P2 M Fried Crossing Regularity has Deriv At slice   8fe3429faa04 construction uses the P2 M Fried Crossing Regularity has Deriv At slice   8fe3429faa04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L136-L142
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L136-L142

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04 {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) :
    HasDerivAt (fun t => f θ t) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1)) τ := by sorry

alias «FriedCrossing».«Regularity».«hasDerivAt_slice_τ» := P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04

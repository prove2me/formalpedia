-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2
-- name    : P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:39.299856+00:00
-- url     : https://prove2.me/theorems/48b76c61-896a-4823-8f7f-b5f7561510ea
-- title:
--   P2 M Fried Crossing Regularity has Deriv At slice   71b076f77be2: P2 M Fried Crossing Regularity has Deriv At slice   71b076f77be2
-- statement:
--   The P2 M Fried Crossing Regularity has Deriv At slice   71b076f77be2 construction uses the P2 M Fried Crossing Regularity has Deriv At slice   71b076f77be2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L144-L150
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L144-L150

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2 {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) :
    HasDerivAt (fun s => f s τ) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0)) θ := by sorry

alias «FriedCrossing».«Regularity».«hasDerivAt_slice_θ» := P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2

-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02
-- name    : P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:30.434132+00:00
-- url     : https://prove2.me/theorems/c30dc0c5-ba03-47ae-be6c-b2a26eeb03ca
-- title:
--   P2 M Fried Crossing Regularity has Deriv At p  e5b14daf2b02: P2 M Fried Crossing Regularity has Deriv At p  e5b14daf2b02
-- statement:
--   The P2 M Fried Crossing Regularity has Deriv At p  e5b14daf2b02 construction uses the P2 M Fried Crossing Regularity has Deriv At p  e5b14daf2b02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L164-L166
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L164-L166

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02 {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun s => f s τ) (pθ f θ τ) θ := by sorry

alias «FriedCrossing».«Regularity».«hasDerivAt_pθ» := P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02

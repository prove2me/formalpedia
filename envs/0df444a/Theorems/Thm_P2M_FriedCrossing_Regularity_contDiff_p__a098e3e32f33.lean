-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33
-- name    : P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:07.927151+00:00
-- url     : https://prove2.me/theorems/e4e66773-e3c7-577d-b594-27b02fba1176
-- title:
--   P2 M Fried Crossing Regularity cont Diff p  a098e3e32f33: P2 M Fried Crossing Regularity cont Diff p  a098e3e32f33
-- statement:
--   The P2 M Fried Crossing Regularity cont Diff p  a098e3e32f33 construction uses the P2 M Fried Crossing Regularity cont Diff p  a098e3e32f33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L184-L192
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L184-L192

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33 {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    ContDiff ℝ m fun q : ℝ × ℝ => pθ f q.1 q.2 := by sorry

alias «FriedCrossing».«Regularity».«contDiff_pθ» := P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33

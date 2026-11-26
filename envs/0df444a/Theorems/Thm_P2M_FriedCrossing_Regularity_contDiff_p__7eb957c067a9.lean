-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9
-- name    : P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:41:23.72277+00:00
-- url     : https://prove2.me/theorems/d8ae0221-b096-4ee7-a4ed-9e867ca10d50
-- title:
--   P2 M Fried Crossing Regularity cont Diff p  7eb957c067a9: P2 M Fried Crossing Regularity cont Diff p  7eb957c067a9
-- statement:
--   One derivative down: the τ-partial of a jointly C^{m+1} function is jointly C^m.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L174-L182
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L174-L182

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9 {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    ContDiff ℝ m fun q : ℝ × ℝ => pτ f q.1 q.2 := by sorry

alias «FriedCrossing».«Regularity».«contDiff_pτ» := P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9

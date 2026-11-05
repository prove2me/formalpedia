-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_keptApart_outside
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.keptApart_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:11:16.942063+00:00
-- url     : https://prove2.me/theorems/c7bf11ae-d7c3-4b96-83c1-afa6c0d0d425
-- title:
--   keptApart_outside
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L52-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L52-L59

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.keptApart_outside {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by sorry

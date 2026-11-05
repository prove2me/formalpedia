-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_writeRecord_before
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.writeRecord_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:58.847469+00:00
-- url     : https://prove2.me/theorems/062e28e9-a6a8-4c25-b520-27f8bb3c13f4
-- title:
--   writeRecord_before
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L68-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L68-L80

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.writeRecord_before {μ : ℕ → ℤ} {dst stride n j k N low high m T active bv nv bi ni : ℕ}
    {w z : ℤ} (hs : 0<stride) (hk : k<j) (hj : j<n)
    (H : RecordAt μ dst stride n k N low high m T active bv nv bi ni) :
    RecordAt (writeRecord μ dst stride n j w z) dst stride n k N low high m T active bv nv bi ni := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_before
-- name    : ThreeSum.LightWeightedPredecessorTable.writeRecord_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:40.879751+00:00
-- url     : https://prove2.me/theorems/c3966365-af66-4e87-92c0-fe64b23fbd9d
-- title:
--   Light Weighted Predecessor Table: write Record before
-- statement:
--   The Light Weighted Predecessor Table construction uses the write Record before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L68-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L68-L80

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessorTable.writeRecord_before {μ : ℕ → ℤ} {dst stride n j k N low high m T active bv nv bi ni : ℕ}
    {w z : ℤ} (hs : 0<stride) (hk : k<j) (hj : j<n)
    (H : RecordAt μ dst stride n k N low high m T active bv nv bi ni) :
    RecordAt (writeRecord μ dst stride n j w z) dst stride n k N low high m T active bv nv bi ni := by sorry

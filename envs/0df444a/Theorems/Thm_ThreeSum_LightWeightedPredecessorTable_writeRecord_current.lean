-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_current
-- name    : ThreeSum.LightWeightedPredecessorTable.writeRecord_current
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:32.094239+00:00
-- url     : https://prove2.me/theorems/d3f9094a-2a99-4b41-a853-5f804b0372ab
-- title:
--   Light Weighted Predecessor Table: write Record current
-- statement:
--   The Light Weighted Predecessor Table construction uses the write Record current property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L61-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L61-L66

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessorTable.writeRecord_current {μ : ℕ → ℤ} {dst stride n j N low high m T active bv nv bi ni : ℕ}
    (hs : 0<stride) (hj : j<n) :
    RecordAt (writeRecord μ dst stride n j (weight N low high m active)
      (key N low high m T active bv nv bi ni)) dst stride n j N low high m T active bv nv bi ni := by sorry

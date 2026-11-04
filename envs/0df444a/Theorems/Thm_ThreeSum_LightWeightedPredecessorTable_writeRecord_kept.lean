-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_kept
-- name    : ThreeSum.LightWeightedPredecessorTable.writeRecord_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:44.337569+00:00
-- url     : https://prove2.me/theorems/043dc87f-edc1-4429-95e6-aa605e66740e
-- title:
--   Light Weighted Predecessor Table: write Record kept
-- statement:
--   The Light Weighted Predecessor Table construction uses the write Record kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L46-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L46-L50

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessorTable.writeRecord_kept {μ : ℕ → ℤ} {dst stride n j : ℕ} {w k : ℤ} (hj : j<n) :
    KeptApart μ (writeRecord μ dst stride n j w k) dst stride n := by sorry

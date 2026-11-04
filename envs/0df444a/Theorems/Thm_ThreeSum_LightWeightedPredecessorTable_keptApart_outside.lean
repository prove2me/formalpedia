-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_keptApart_outside
-- name    : ThreeSum.LightWeightedPredecessorTable.keptApart_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:42.05119+00:00
-- url     : https://prove2.me/theorems/aa04333b-074f-4938-8383-57f215ac16d2
-- title:
--   Light Weighted Predecessor Table: kept Apart outside
-- statement:
--   The Light Weighted Predecessor Table construction uses the kept Apart outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L52-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L52-L59

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessorTable.keptApart_outside {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by sorry

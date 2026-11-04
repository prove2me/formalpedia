-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
-- name    : ThreeSum.LightWeightedPredecessorTable.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:47.878101+00:00
-- url     : https://prove2.me/theorems/811294ab-8567-4aea-baf1-63fbf02d102d
-- title:
--   Light Weighted Predecessor Table: time bound
-- statement:
--   The Light Weighted Predecessor Table construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L222-L236
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L222-L236

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedPredecessorTable.time_bound (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by sorry

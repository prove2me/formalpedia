-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound
-- name    : ThreeSum.LightWeightedPredecessor.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:36.782206+00:00
-- url     : https://prove2.me/theorems/d0d2816e-eb15-4c64-bec6-cf32f059eba1
-- title:
--   Light Weighted Predecessor: time bound
-- statement:
--   The Light Weighted Predecessor construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L235-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L235-L238

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedPredecessor.time_bound (N L : ℕ) : time N L≤3000*(N+L+1)^2 := by sorry

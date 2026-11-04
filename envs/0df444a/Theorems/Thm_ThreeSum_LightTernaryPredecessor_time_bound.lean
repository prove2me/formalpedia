-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
-- name    : ThreeSum.LightTernaryPredecessor.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:48.037384+00:00
-- url     : https://prove2.me/theorems/b541a3d6-848b-47dd-8cc4-de86cb38b0bc
-- title:
--   Light Ternary Predecessor: time bound
-- statement:
--   The Light Ternary Predecessor construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L229-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L229-L232

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryPredecessor.time_bound (N L : ℕ) : time N L≤3000*(N+L+1)^2 := by sorry

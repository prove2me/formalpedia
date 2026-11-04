-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
-- name    : ThreeSum.LightTernaryRankTable.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:49.546804+00:00
-- url     : https://prove2.me/theorems/40d498f2-f0ce-488c-a612-789c01c5d2ea
-- title:
--   Light Ternary Rank Table: time bound
-- statement:
--   The Light Ternary Rank Table construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L122-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L122-L124

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryRankTable.time_bound (N n : ℕ) : time N n ≤ 2000*(N+1)^2*(n+1) := by sorry

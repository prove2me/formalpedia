-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
-- name    : ThreeSum.LightTernaryPredecessorTable.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:20.304808+00:00
-- url     : https://prove2.me/theorems/a5f2476c-5f95-45bf-8fb3-33fdc65ff4c8
-- title:
--   Light Ternary Predecessor Table: time bound
-- statement:
--   The Light Ternary Predecessor Table construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L217-L231
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L217-L231

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryPredecessorTable.time_bound (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by sorry

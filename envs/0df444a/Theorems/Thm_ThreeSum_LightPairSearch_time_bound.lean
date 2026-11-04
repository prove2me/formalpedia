-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_time_bound
-- name    : ThreeSum.LightPairSearch.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:09.012051+00:00
-- url     : https://prove2.me/theorems/14a75f2b-2e04-43dc-ac6d-9ffc64193b87
-- title:
--   Light Pair Search: time bound
-- statement:
--   The Light Pair Search construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L56-L59

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightPairSearch.time_bound (q T : ℕ) (hq : 0<q) : time q T≤q*q*(T+200)+100 := by sorry

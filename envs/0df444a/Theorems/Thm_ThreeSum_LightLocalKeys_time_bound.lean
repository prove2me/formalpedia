-- Prove2me | Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
-- name    : ThreeSum.LightLocalKeys.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:39.405337+00:00
-- url     : https://prove2.me/theorems/fb62b4df-a305-4423-b5d2-b4ac153a04a8
-- title:
--   Light Local Keys: time bound
-- statement:
--   The Light Local Keys construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeys.lean#L138-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeys.lean#L138-L148

import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeys
open Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalKeys.time_bound (L n rows : ℕ) : time L n rows ≤ 1200*(L+1)*(n+1)*(rows+1) := by sorry

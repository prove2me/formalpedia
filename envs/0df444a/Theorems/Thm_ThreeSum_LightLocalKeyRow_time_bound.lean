-- Prove2me | Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
-- name    : ThreeSum.LightLocalKeyRow.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:36.310376+00:00
-- url     : https://prove2.me/theorems/c0ad7775-3734-459d-ae6d-8596fa921452
-- title:
--   Light Local Key Row: time bound
-- statement:
--   The Light Local Key Row construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeyRow.lean#L146-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeyRow.lean#L146-L149

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeyRow
open Light LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalKeyRow.time_bound (L n : ℕ) : time L n ≤ 950*(L+1)*(n+1) := by sorry

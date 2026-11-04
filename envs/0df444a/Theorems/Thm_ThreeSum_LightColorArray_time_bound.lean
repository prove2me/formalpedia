-- Prove2me | Theorems.Thm_ThreeSum_LightColorArray_time_bound
-- name    : ThreeSum.LightColorArray.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:41.541198+00:00
-- url     : https://prove2.me/theorems/d2699ea6-83f4-455f-9e96-1a718c0c6c2c
-- title:
--   Light Color Array: time bound
-- statement:
--   The Light Color Array construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L115-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L115-L117

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightColorArray.time_bound (W n : ℕ) : time W n ≤ 600*(W+1)*(n+1) := by sorry

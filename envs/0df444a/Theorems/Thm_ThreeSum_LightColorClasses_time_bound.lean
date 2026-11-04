-- Prove2me | Theorems.Thm_ThreeSum_LightColorClasses_time_bound
-- name    : ThreeSum.LightColorClasses.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:06.443306+00:00
-- url     : https://prove2.me/theorems/f36466d7-8250-43c5-9fb2-3529b7fa6915
-- title:
--   Light Color Classes: time bound
-- statement:
--   The Light Color Classes construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorClasses.lean#L156-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorClasses.lean#L156-L159

import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorClasses
open Light ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightColorClasses.time_bound (W n : ℕ) : time W n ≤ 1200*(W+1)*(n+1) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_time_bound
-- name    : ThreeSum.LightNormalize.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:39.580036+00:00
-- url     : https://prove2.me/theorems/e654b832-59b5-4d04-8a14-40747f43fe4f
-- title:
--   Light Normalize: time bound
-- statement:
--   The Light Normalize construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L190-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L190-L193

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightNormalize.time_bound (n : ℕ) : time n ≤ 400*(n+1)*(Nat.clog 2 n+1) := by sorry

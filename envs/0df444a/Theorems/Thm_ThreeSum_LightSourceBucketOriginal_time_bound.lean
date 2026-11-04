-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketOriginal_time_bound
-- name    : ThreeSum.LightSourceBucketOriginal.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:54.641797+00:00
-- url     : https://prove2.me/theorems/fb96ddf0-7ab4-47e0-9156-c948e375d4ee
-- title:
--   Light Source Bucket Original: time bound
-- statement:
--   The Light Source Bucket Original construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOriginal.lean#L91-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOriginal.lean#L91-L96

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketOriginal.time_bound (N p m U D : ℕ) :
    time N p m U D ≤ 498*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333 := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketSetup_time_bound
-- name    : ThreeSum.LightSourceBucketSetup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:43.126987+00:00
-- url     : https://prove2.me/theorems/cfd71197-5cb4-4051-8011-215f9ea0087f
-- title:
--   Light Source Bucket Setup: time bound
-- statement:
--   The Light Source Bucket Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketSetup.lean#L82-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketSetup.lean#L82-L85

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketSetup.time_bound (N M : ℕ) : time N M ≤ 500*(N+M+1) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
-- name    : ThreeSum.LightSourceBucketBuild.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:44.848229+00:00
-- url     : https://prove2.me/theorems/a45b31be-74b3-40cf-a27e-e4b7e12dbdfd
-- title:
--   Light Source Bucket Build: time bound
-- statement:
--   The Light Source Bucket Build construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketBuild.lean#L79-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketBuild.lean#L79-L82

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketBuild.time_bound (N M : ℕ) : time N M ≤ 300*(N+M+1) := by sorry

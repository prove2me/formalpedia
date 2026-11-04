-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
-- name    : ThreeSum.LightSourceBucketFromHistogram.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:47.374676+00:00
-- url     : https://prove2.me/theorems/e5380410-6126-4029-ab60-c983a98dd930
-- title:
--   Light Source Bucket From Histogram: time bound
-- statement:
--   The Light Source Bucket From Histogram construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketFromHistogram.lean#L79-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketFromHistogram.lean#L79-L81

import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketFromHistogram
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketFromHistogram.time_bound (N M : ℕ) : time N M ≤ 220*(N+M+1) := by sorry

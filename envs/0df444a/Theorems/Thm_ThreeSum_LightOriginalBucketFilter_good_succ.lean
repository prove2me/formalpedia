-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_succ
-- name    : ThreeSum.LightOriginalBucketFilter.good_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:38.238517+00:00
-- url     : https://prove2.me/theorems/30db7d3b-b532-4396-8b31-308e86966bee
-- title:
--   Light Original Bucket Filter: good succ
-- statement:
--   The Light Original Bucket Filter construction uses the good succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L23-L25

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem ThreeSum.LightOriginalBucketFilter.good_succ (keys counts : ℕ → ℕ) (n : ℕ) :
    good keys counts (n+1)=good keys counts n++if counts (keys n)=1 then [n] else [] := by sorry

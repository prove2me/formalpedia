-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_succ
-- name    : ThreeSum.LightOriginalBucketFilter.bad_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:43.18429+00:00
-- url     : https://prove2.me/theorems/005172d5-a309-437c-80bf-56036947e959
-- title:
--   Light Original Bucket Filter: bad succ
-- statement:
--   The Light Original Bucket Filter construction uses the bad succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L27-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L27-L29

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem ThreeSum.LightOriginalBucketFilter.bad_succ (keys counts : ℕ → ℕ) (n : ℕ) :
    bad keys counts (n+1)=bad keys counts n++if counts (keys n)=1 then [] else [n] := by sorry

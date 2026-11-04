-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalBucketFilter_lengths
-- name    : ThreeSum.LightOriginalBucketFilter.lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:17.286258+00:00
-- url     : https://prove2.me/theorems/83ec6c1a-838d-45fa-a3e4-32b287524afe
-- title:
--   Light Original Bucket Filter: lengths
-- statement:
--   The Light Original Bucket Filter construction uses the lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L19-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L19-L21

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem ThreeSum.LightOriginalBucketFilter.lengths (keys counts : ℕ → ℕ) (n : ℕ) :
    (good keys counts n).length≤n ∧ (bad keys counts n).length≤n := by sorry

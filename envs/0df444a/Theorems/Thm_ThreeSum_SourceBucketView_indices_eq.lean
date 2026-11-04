-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_indices_eq
-- name    : ThreeSum.SourceBucketView.indices_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:08.421603+00:00
-- url     : https://prove2.me/theorems/4f3694f9-cdb8-4ade-8b06-c21c27e5a973
-- title:
--   Source Bucket View: indices eq
-- statement:
--   The Source Bucket View construction uses the indices eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L32-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L32-L35

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    indices μ offsets flat r = bucketList μ flat (offset key N r) (count key r N) := by sorry

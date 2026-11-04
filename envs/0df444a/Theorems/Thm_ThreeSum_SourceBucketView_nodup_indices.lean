-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_nodup_indices
-- name    : ThreeSum.SourceBucketView.nodup_indices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:55.220677+00:00
-- url     : https://prove2.me/theorems/3836ae9f-7072-4889-ab0d-0ff5d09dc9e4
-- title:
--   Source Bucket View: nodup indices
-- statement:
--   The Source Bucket View construction uses the nodup indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L48-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L48-L52

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.nodup_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (indices μ offsets flat r).Nodup := by sorry

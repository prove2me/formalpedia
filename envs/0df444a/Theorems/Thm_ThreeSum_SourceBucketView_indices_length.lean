-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_indices_length
-- name    : ThreeSum.SourceBucketView.indices_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:33.75144+00:00
-- url     : https://prove2.me/theorems/6857d5b9-1b21-4787-bf9a-3115f7054a2e
-- title:
--   Source Bucket View: indices length
-- statement:
--   The Source Bucket View construction uses the indices length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L37-L40

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.indices_length {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    (indices μ offsets flat r).length = count key r N := by sorry

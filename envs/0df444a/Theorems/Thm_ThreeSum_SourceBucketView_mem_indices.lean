-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_mem_indices
-- name    : ThreeSum.SourceBucketView.mem_indices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:44.179296+00:00
-- url     : https://prove2.me/theorems/00bb3358-2639-42f8-a1b0-79c8246cce03
-- title:
--   Source Bucket View: mem indices
-- statement:
--   The Source Bucket View construction uses the mem indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L42-L46

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.mem_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ indices μ offsets flat r ↔ i < N ∧ key i = r := by sorry

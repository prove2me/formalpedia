-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_start_eq
-- name    : ThreeSum.SourceBucketView.start_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:30:55.783823+00:00
-- url     : https://prove2.me/theorems/f9dffb17-f647-432d-9d96-8e3c9d376d2f
-- title:
--   Source Bucket View: start eq
-- statement:
--   The Source Bucket View construction uses the start eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L15-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L15-L18

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r ≤ M) :
    start μ offsets r = offset key N r := by sorry

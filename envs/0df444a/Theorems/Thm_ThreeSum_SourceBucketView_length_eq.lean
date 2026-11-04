-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_length_eq
-- name    : ThreeSum.SourceBucketView.length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:28.938092+00:00
-- url     : https://prove2.me/theorems/07c83b68-1440-439a-975a-8b6a5d221ad2
-- title:
--   Source Bucket View: length eq
-- statement:
--   The Source Bucket View construction uses the length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L26-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L26-L30

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    length μ offsets r = count key r N := by sorry

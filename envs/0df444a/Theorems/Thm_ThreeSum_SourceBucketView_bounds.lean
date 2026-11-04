-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_bounds
-- name    : ThreeSum.SourceBucketView.bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:10.657799+00:00
-- url     : https://prove2.me/theorems/596c695d-bc08-41fe-92cf-d91bfe8c45e1
-- title:
--   Source Bucket View: bounds
-- statement:
--   The Source Bucket View construction uses the bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L54-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L54-L58

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.bounds {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    start μ offsets r ≤ stop μ offsets r ∧ stop μ offsets r ≤ N := by sorry

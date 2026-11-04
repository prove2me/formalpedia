-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_read
-- name    : ThreeSum.SourceBucketView.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:30:56.105808+00:00
-- url     : https://prove2.me/theorems/1f0d92fd-a4c9-45d9-b683-bb7b46018d50
-- title:
--   Source Bucket View: read
-- statement:
--   The Source Bucket View construction uses the read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L60-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L60-L67

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.read {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < length μ offsets r) :
    ∃ i < N, key i = r ∧ μ (flat+start μ offsets r+t) = (i : ℤ) := by sorry

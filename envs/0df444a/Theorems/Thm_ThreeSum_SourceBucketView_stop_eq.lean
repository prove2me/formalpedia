-- Prove2me | Theorems.Thm_ThreeSum_SourceBucketView_stop_eq
-- name    : ThreeSum.SourceBucketView.stop_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:32.462395+00:00
-- url     : https://prove2.me/theorems/4a3967f8-2ee3-4323-b36a-ca08cbf72e0c
-- title:
--   Source Bucket View: stop eq
-- statement:
--   The Source Bucket View construction uses the stop eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L20-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean#L20-L24

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram

theorem ThreeSum.SourceBucketView.stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    stop μ offsets r = offset key N (r+1) := by sorry

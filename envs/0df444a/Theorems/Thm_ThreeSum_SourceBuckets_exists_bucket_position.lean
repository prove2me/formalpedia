-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_exists_bucket_position
-- name    : ThreeSum.SourceBuckets.exists_bucket_position
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:55.74146+00:00
-- url     : https://prove2.me/theorems/6f4a2a40-705c-4585-891b-d6bd3b555d00
-- title:
--   Source Buckets: exists bucket position
-- statement:
--   The Source Buckets construction uses the exists bucket position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L119-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L119-L130

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem ThreeSum.SourceBuckets.exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t := by sorry

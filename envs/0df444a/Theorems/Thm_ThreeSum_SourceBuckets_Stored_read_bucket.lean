-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_Stored_read_bucket
-- name    : ThreeSum.SourceBuckets.Stored.read_bucket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:17.330327+00:00
-- url     : https://prove2.me/theorems/e9c20fa6-8a0c-49ef-b6b5-ced97b757e12
-- title:
--   Stored: read bucket
-- statement:
--   The Stored construction uses the read bucket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L143-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L143-L150

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

theorem ThreeSum.SourceBuckets.Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t ∧
      μ (flat+offset key N r+t) = (i : ℤ) := by sorry

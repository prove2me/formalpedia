-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_Stored_offsets_end
-- name    : ThreeSum.SourceBuckets.Stored.offsets_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:36.720196+00:00
-- url     : https://prove2.me/theorems/5c9d3d14-aada-4ed5-aa67-02c79dc1524c
-- title:
--   Stored: offsets end
-- statement:
--   The Stored construction uses the offsets end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L183-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L183-L188

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

theorem ThreeSum.SourceBuckets.Stored.offsets_end {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) :
    μ offsets = 0 ∧ μ (offsets+M) = (N : ℤ) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_Stored_mem_bucketList_w3sum_ac885d1
-- name    : ThreeSum.SourceBuckets.Stored.mem_bucketList_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:01.050196+00:00
-- url     : https://prove2.me/theorems/3ec9ad9b-5f3c-471c-9fde-2ee14d8bdc39
-- title:
--   Stored: mem bucket List
-- statement:
--   The Stored construction uses the mem bucket List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L152-L168
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L152-L168

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

theorem ThreeSum.SourceBuckets.Stored.mem_bucketList_w3sum_ac885d1 {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ bucketList μ flat (offset key N r) (count key r N) ↔ i < N ∧ key i = r := by sorry

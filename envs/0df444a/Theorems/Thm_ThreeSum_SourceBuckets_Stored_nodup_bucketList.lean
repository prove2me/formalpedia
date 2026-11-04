-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_Stored_nodup_bucketList
-- name    : ThreeSum.SourceBuckets.Stored.nodup_bucketList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:57.749774+00:00
-- url     : https://prove2.me/theorems/7b1926ca-d9ba-4ea2-add9-bb999cd7455c
-- title:
--   Stored: nodup bucket List
-- statement:
--   The Stored construction uses the nodup bucket List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L170-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L170-L181

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

theorem ThreeSum.SourceBuckets.Stored.nodup_bucketList {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (bucketList μ flat (offset key N r) (count key r N)).Nodup := by sorry

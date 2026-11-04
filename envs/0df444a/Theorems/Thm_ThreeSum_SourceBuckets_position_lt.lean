-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_lt
-- name    : ThreeSum.SourceBuckets.position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:47.554661+00:00
-- url     : https://prove2.me/theorems/94f16c8c-ea02-4e12-a8d8-08f132f2e9bb
-- title:
--   Source Buckets: position lt
-- statement:
--   The Source Buckets construction uses the position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L68-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L68-L70

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

theorem ThreeSum.SourceBuckets.position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N := by sorry

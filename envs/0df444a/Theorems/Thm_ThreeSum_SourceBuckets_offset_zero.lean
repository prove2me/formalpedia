-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
-- name    : ThreeSum.SourceBuckets.offset_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:10.609008+00:00
-- url     : https://prove2.me/theorems/c97d8f7d-032a-4463-9150-6189622de06a
-- title:
--   Source Buckets: offset zero
-- statement:
--   The Source Buckets construction uses the offset zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L24-L25

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

theorem ThreeSum.SourceBuckets.offset_zero (key : ℕ → ℕ) (N : ℕ) : offset key N 0 = 0 := by sorry

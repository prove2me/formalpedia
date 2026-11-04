-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_start
-- name    : ThreeSum.SourceBuckets.position_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:35.277298+00:00
-- url     : https://prove2.me/theorems/5f00a002-e4ab-41b6-a567-87a433d7d98c
-- title:
--   Source Buckets: position start
-- statement:
--   The Source Buckets construction uses the position start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L60-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L60-L61

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

theorem ThreeSum.SourceBuckets.position_start (key : ℕ → ℕ) (N i : ℕ) :
    offset key N (key i) ≤ position key N i := by sorry

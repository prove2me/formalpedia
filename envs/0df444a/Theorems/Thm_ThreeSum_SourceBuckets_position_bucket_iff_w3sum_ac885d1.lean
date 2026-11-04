-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff_w3sum_ac885d1
-- name    : ThreeSum.SourceBuckets.position_bucket_iff_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:07.696194+00:00
-- url     : https://prove2.me/theorems/ca2a8d87-17be-4f51-ba35-932173e99bb0
-- title:
--   Source Buckets: position bucket iff
-- statement:
--   The Source Buckets construction uses the position bucket iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L95-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L95-L108

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

theorem ThreeSum.SourceBuckets.position_bucket_iff_w3sum_ac885d1 {key : ℕ → ℕ} {N i r : ℕ} (hi : i < N) :
    offset key N r ≤ position key N i ∧ position key N i < offset key N (r+1) ↔ key i = r := by sorry

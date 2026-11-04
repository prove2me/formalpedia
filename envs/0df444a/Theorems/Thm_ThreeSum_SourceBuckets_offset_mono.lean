-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_offset_mono
-- name    : ThreeSum.SourceBuckets.offset_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:24.028381+00:00
-- url     : https://prove2.me/theorems/04393f2f-44cd-45d5-bca6-ed32a5b6b8b6
-- title:
--   Source Buckets: offset mono
-- statement:
--   The Source Buckets construction uses the offset mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L31-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L31-L33

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

theorem ThreeSum.SourceBuckets.offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by sorry

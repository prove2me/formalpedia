-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_lt_of_key_lt
-- name    : ThreeSum.SourceBuckets.position_lt_of_key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:09.810316+00:00
-- url     : https://prove2.me/theorems/5c3a92c4-c6cd-4bad-ba0e-95ba8c803de1
-- title:
--   Source Buckets: position lt of key lt
-- statement:
--   The Source Buckets construction uses the position lt of key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L72-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L72-L74

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

theorem ThreeSum.SourceBuckets.position_lt_of_key_lt {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hij : key i < key j) : position key N i < position key N j := by sorry

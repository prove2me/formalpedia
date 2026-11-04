-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_represents
-- name    : ThreeSum.LocalHashMoments.localSchedule_represents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:28.38622+00:00
-- url     : https://prove2.me/theorems/9bd10aea-954a-4740-8edf-bb31687cf7bc
-- title:
--   Local Hash Moments: local Schedule represents
-- statement:
--   The Local Hash Moments construction uses the local Schedule represents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L305-L311
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L305-L311

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}

theorem ThreeSum.LocalHashMoments.localSchedule_represents {h : ℕ} (hh : 0 < h) (a b : LocalField h) :
    ∃ w ∈ localSchedule h, ∃ e : Edge (512 * h) h,
      HashFamily.hashValue w (left e) = a ∧ HashFamily.hashValue w (right e) = b ∧
      HashFamily.bucketSize (leftVertices (512 * h) h) w a ≤ localBucketCap h ∧
      HashFamily.bucketSize (rightVertices (512 * h) h) w b ≤ localBucketCap h := by sorry

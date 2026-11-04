-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_length
-- name    : ThreeSum.LocalHashMoments.localSchedule_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:24.776203+00:00
-- url     : https://prove2.me/theorems/a982cfdd-b579-4e81-ab6b-0668c2872133
-- title:
--   Local Hash Moments: local Schedule length
-- statement:
--   The Local Hash Moments construction uses the local Schedule length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L285-L289
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L285-L289

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

theorem ThreeSum.LocalHashMoments.localSchedule_length (h : ℕ) :
    (localSchedule h).length =
      320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1) := by sorry

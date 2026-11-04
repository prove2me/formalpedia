-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_schedule_covers
-- name    : ThreeSum.LocalHashMoments.schedule_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:32.55757+00:00
-- url     : https://prove2.me/theorems/ce4ba3bc-0cc2-41b7-9955-18cd1f923b7b
-- title:
--   Local Hash Moments: schedule covers
-- statement:
--   The deterministic, actually defined schedule covers all ordered targets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L235-L252
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L235-L252

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

theorem ThreeSum.LocalHashMoments.schedule_covers (values : List K) (hvalues : ∀ x, x ∈ values)
    (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    ∃ w ∈ schedule L h values,
      Covers L h (bucketBound L h (Fintype.card K)) w target := by sorry

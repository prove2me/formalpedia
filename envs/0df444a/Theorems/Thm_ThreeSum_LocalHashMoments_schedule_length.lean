-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_schedule_length
-- name    : ThreeSum.LocalHashMoments.schedule_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:28.141518+00:00
-- url     : https://prove2.me/theorems/70d63ec5-8801-4e02-a934-b68e823ce7d3
-- title:
--   Local Hash Moments: schedule length
-- statement:
--   The Local Hash Moments construction uses the schedule length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L230-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L230-L232

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

theorem ThreeSum.LocalHashMoments.schedule_length (values : List K) :
    (schedule L h values).length = scheduleLength h (Fintype.card K) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_cons
-- name    : ThreeSum.TernaryMomentSchedule.aggregate_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:45.404874+00:00
-- url     : https://prove2.me/theorems/0af739f6-a24c-48e3-8d01-909b32393656
-- title:
--   Ternary Moment Schedule: aggregate cons
-- statement:
--   The Ternary Moment Schedule construction uses the aggregate cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L20-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L20-L23

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.aggregate_cons (c : ℕ×ℕ) (xs : List (ℕ×ℕ))
    (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate (c::xs) score k i=
      (if c.1=k then score c.1 c.2 i else 0)+aggregate xs score k i := by sorry

attribute [defeq] ThreeSum.TernaryMomentSchedule.aggregate_cons

-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_append
-- name    : ThreeSum.TernaryMomentSchedule.aggregate_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:42.843226+00:00
-- url     : https://prove2.me/theorems/8d2df7b4-3b7d-425d-a65c-6bafb1366c22
-- title:
--   Ternary Moment Schedule: aggregate append
-- statement:
--   The Ternary Moment Schedule construction uses the aggregate append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L25-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L25-L28

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.aggregate_append (xs ys : List (ℕ×ℕ))
    (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate (xs++ys) score k i=aggregate xs score k i+aggregate ys score k i := by sorry

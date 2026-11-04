-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_same_type_cost
-- name    : ThreeSum.WeightedSchedule.same_type_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:37.925444+00:00
-- url     : https://prove2.me/theorems/eae22e5d-7217-485c-a5cf-dc749366e8d2
-- title:
--   Weighted Schedule: same type cost
-- statement:
--   The Weighted Schedule construction uses the same type cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L53-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L53-L55

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.same_type_cost {N : ℕ} {Q R : TritWord N} {π : DigitType}
    (hQ : HasType Q π) (hR : HasType R π) : cacheCost Q=cacheCost R := by sorry

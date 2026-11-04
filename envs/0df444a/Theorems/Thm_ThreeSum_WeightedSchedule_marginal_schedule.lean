-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_marginal_schedule
-- name    : ThreeSum.WeightedSchedule.marginal_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:41.954184+00:00
-- url     : https://prove2.me/theorems/f19d96ec-6d27-4e3d-b1dd-fb8b88e4902d
-- title:
--   Weighted Schedule: marginal schedule
-- statement:
--   The Weighted Schedule construction uses the marginal schedule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L30-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L30-L33

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.marginal_schedule (m : ℕ) :
    fixedAlpha m 0=fixedPi m 0+fixedPi m 1/2+fixedPi m 2/3 ∧
    fixedAlpha m 1=fixedPi m 1/2+fixedPi m 2/3 := by sorry

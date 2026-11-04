-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_output_cost
-- name    : ThreeSum.WeightedSchedule.output_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:18.72984+00:00
-- url     : https://prove2.me/theorems/f17c7f46-a0f7-4584-9185-fb78449dc9f7
-- title:
--   Weighted Schedule: output cost
-- statement:
--   The Weighted Schedule construction uses the output cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L67-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L67-L70

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.output_cost {m : ℕ} {Q : TritWord (fixedLength m)}
    (hQ : HasType Q (fixedPi m)) : cacheCost Q=bankCut m+dropBudget m := by sorry

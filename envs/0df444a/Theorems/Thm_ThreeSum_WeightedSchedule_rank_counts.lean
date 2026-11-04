-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_rank_counts
-- name    : ThreeSum.WeightedSchedule.rank_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:13.116365+00:00
-- url     : https://prove2.me/theorems/6adb99ee-79ce-493d-a2d8-4e8fed56fc49
-- title:
--   Weighted Schedule: rank counts
-- statement:
--   The Weighted Schedule construction uses the rank counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L44-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L44-L51

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.rank_counts {N : ℕ} (Q : TritWord N) :
    TernaryBank.rank Q=digitCount Q 1+2*digitCount Q 2 := by sorry

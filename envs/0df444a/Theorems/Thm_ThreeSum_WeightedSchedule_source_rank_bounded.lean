-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_source_rank_bounded
-- name    : ThreeSum.WeightedSchedule.source_rank_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:28.695289+00:00
-- url     : https://prove2.me/theorems/9ebcc0b7-f581-4d30-98a0-beec8bb2dcbf
-- title:
--   Weighted Schedule: source rank bounded
-- statement:
--   The Weighted Schedule construction uses the source rank bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L83-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L83-L84

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.source_rank_bounded (m : ℕ) : sourceRank m≤2*fixedLength m := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_output_rank
-- name    : ThreeSum.WeightedSchedule.output_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:47.579756+00:00
-- url     : https://prove2.me/theorems/d40553a3-212f-48b4-bb27-29ff1f9ba78a
-- title:
--   Weighted Schedule: output rank
-- statement:
--   The Weighted Schedule construction uses the output rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L62-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L62-L65

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.output_rank {m : ℕ} {Q : TritWord (fixedLength m)}
    (hQ : HasType Q (fixedPi m)) : TernaryBank.rank Q=2*sourceRank m := by sorry

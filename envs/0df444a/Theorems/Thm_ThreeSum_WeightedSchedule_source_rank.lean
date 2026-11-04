-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_source_rank
-- name    : ThreeSum.WeightedSchedule.source_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:17.45089+00:00
-- url     : https://prove2.me/theorems/5b074ca9-a6bf-4358-8549-e3427358f408
-- title:
--   Weighted Schedule: source rank
-- statement:
--   The Weighted Schedule construction uses the source rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L57-L60

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.source_rank {m : ℕ} {A : TritWord (fixedLength m)}
    (hA : HasType A (fixedAlpha m)) : TernaryBank.rank A=sourceRank m := by sorry

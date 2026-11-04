-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_fixedAlpha_total
-- name    : ThreeSum.WeightedSchedule.fixedAlpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:45.941648+00:00
-- url     : https://prove2.me/theorems/ff1ec8e2-8d6d-4775-879a-cfeb167c1bcc
-- title:
--   Weighted Schedule: fixed Alpha total
-- statement:
--   The Weighted Schedule construction uses the fixed Alpha total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L24-L25

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.fixedAlpha_total (m : ℕ) : ∑ d : Fin 3, fixedAlpha m d = fixedLength m := by sorry

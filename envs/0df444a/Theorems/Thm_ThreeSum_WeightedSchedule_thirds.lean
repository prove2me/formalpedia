-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_thirds
-- name    : ThreeSum.WeightedSchedule.thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:40.22357+00:00
-- url     : https://prove2.me/theorems/eb72f462-e836-4f02-bfa1-76319f2a68ac
-- title:
--   Weighted Schedule: thirds
-- statement:
--   The Weighted Schedule construction uses the thirds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L27-L28

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.thirds (m : ℕ) : fixedPi m 2=3*fixedAlpha m 2 := by sorry

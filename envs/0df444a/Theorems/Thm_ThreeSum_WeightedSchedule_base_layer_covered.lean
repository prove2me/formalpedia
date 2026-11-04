-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_base_layer_covered
-- name    : ThreeSum.WeightedSchedule.base_layer_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:43.637652+00:00
-- url     : https://prove2.me/theorems/321fd7a4-9209-458d-b9b9-e911cfedea7b
-- title:
--   Weighted Schedule: base layer covered
-- statement:
--   The Weighted Schedule construction uses the base layer covered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L80-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L80-L81

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.base_layer_covered (m : ℕ) : 1025*sourceRank m≤2*bankCut m := by sorry

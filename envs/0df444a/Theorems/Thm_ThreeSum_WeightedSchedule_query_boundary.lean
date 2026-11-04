-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_query_boundary
-- name    : ThreeSum.WeightedSchedule.query_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:18.181292+00:00
-- url     : https://prove2.me/theorems/8a723349-24e6-4fc3-8af9-d2b47c789494
-- title:
--   Weighted Schedule: query boundary
-- statement:
--   The Weighted Schedule construction uses the query boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L76-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L76-L78

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.query_boundary {m : ℕ} {Q : TritWord (fixedLength m)}
    (hQ : HasType Q (fixedPi m)) : cacheCost Q+1024-bankCut m=treeBudget m := by sorry

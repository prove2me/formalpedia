-- Prove2me | Theorems.Thm_ThreeSum_WeightedSchedule_query_outside
-- name    : ThreeSum.WeightedSchedule.query_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:44.969692+00:00
-- url     : https://prove2.me/theorems/2c36b2a2-3583-4ed3-88ee-e22e38fd358d
-- title:
--   Weighted Schedule: query outside
-- statement:
--   The Weighted Schedule construction uses the query outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L72-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean#L72-L74

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem ThreeSum.WeightedSchedule.query_outside {m : ℕ} {Q : TritWord (fixedLength m)}
    (hm : 0<m) (hQ : HasType Q (fixedPi m)) : bankCut m<cacheCost Q := by sorry

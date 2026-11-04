-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_reporter_time_bound
-- name    : ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:28:29.080766+00:00
-- url     : https://prove2.me/theorems/63bef51f-1304-48a7-b35c-ad9110924ca1
-- title:
--   Weighted Global Moment Reporter Budget: reporter time bound
-- statement:
--   The Weighted Global Moment Reporter Budget construction uses the reporter time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L96-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L96-L104

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    LightWeightedGlobalMomentReporter.time S H≤reporterConstant H*base S := by sorry

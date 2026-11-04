-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_driver_time_bound
-- name    : ThreeSum.WeightedGlobalMomentReporterBudget.driver_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:28:52.754933+00:00
-- url     : https://prove2.me/theorems/e10126f7-cc0b-451f-9c1a-effe84d153db
-- title:
--   Weighted Global Moment Reporter Budget: driver time bound
-- statement:
--   The Weighted Global Moment Reporter Budget construction uses the driver time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L63-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L63-L91

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem ThreeSum.WeightedGlobalMomentReporterBudget.driver_time_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (terms : ℕ) :
    LightWeightedGlobalCertifiedMomentDriver.time S terms≤driverConstant terms*base S := by sorry

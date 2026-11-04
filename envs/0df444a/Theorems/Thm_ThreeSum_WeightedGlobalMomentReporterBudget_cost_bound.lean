-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_cost_bound
-- name    : ThreeSum.WeightedGlobalMomentReporterBudget.cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:28:21.465564+00:00
-- url     : https://prove2.me/theorems/2079a6ce-4b82-457e-9022-1c245d452129
-- title:
--   Weighted Global Moment Reporter Budget: cost bound
-- statement:
--   The Weighted Global Moment Reporter Budget construction uses the cost bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L41-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L41-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem ThreeSum.WeightedGlobalMomentReporterBudget.cost_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (terms : ℕ) (c : ℕ×ℕ) (hc : c∈channels terms) :
    LightWeightedGlobalCertifiedMomentDriver.cost S c≤weightBudget terms*base S := by sorry

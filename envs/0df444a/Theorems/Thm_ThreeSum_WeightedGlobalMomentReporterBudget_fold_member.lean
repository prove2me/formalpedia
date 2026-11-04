-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_fold_member
-- name    : ThreeSum.WeightedGlobalMomentReporterBudget.fold_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:31:11.076882+00:00
-- url     : https://prove2.me/theorems/d1630d84-3cb3-44a3-b7f1-a6db24a6fca7
-- title:
--   Weighted Global Moment Reporter Budget: fold member
-- statement:
--   The Weighted Global Moment Reporter Budget construction uses the fold member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L29-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L29-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem ThreeSum.WeightedGlobalMomentReporterBudget.fold_member (xs : List (ℕ×ℕ)) (c : ℕ×ℕ) (hc : c∈xs) :
    circuitCost c≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_fold_floor
-- name    : ThreeSum.WeightedGlobalMomentReporterBudget.fold_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:30:05.08405+00:00
-- url     : https://prove2.me/theorems/5c148f06-609f-4dbe-b972-4f1de50247c6
-- title:
--   Weighted Global Moment Reporter Budget: fold floor
-- statement:
--   The Weighted Global Moment Reporter Budget construction uses the fold floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L23-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L23-L27

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem ThreeSum.WeightedGlobalMomentReporterBudget.fold_floor (xs : List (ℕ×ℕ)) :
    1000≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by sorry

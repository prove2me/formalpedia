-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentReporterBudget_fold_member
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.fold_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:36:29.528455+00:00
-- url     : https://prove2.me/theorems/5baed387-00bb-47d7-b75c-c7e8824049aa
-- title:
--   fold_member
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L29-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L29-L36

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.fold_member (xs : List (ℕ×ℕ)) (c : ℕ×ℕ) (hc : c∈xs) :
    circuitCost c≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by sorry

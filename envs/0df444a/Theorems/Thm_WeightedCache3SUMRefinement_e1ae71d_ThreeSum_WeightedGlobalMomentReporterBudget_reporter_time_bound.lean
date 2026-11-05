-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentReporterBudget_reporter_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:36:44.900952+00:00
-- url     : https://prove2.me/theorems/35b3903c-6af4-4b03-a358-c33412ace731
-- title:
--   reporter_time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L96-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentReporterBudget.lean#L96-L104

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    LightWeightedGlobalMomentReporter.time S H≤reporterConstant H*base S := by sorry

-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalMomentReporter_driver_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentReporter.driver_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:30:36.095416+00:00
-- url     : https://prove2.me/theorems/5af1f197-3372-4598-9dbf-1ca4f52e05a9
-- title:
--   driver_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L33-L35

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDriverResources
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentReporter.driver_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    (driver S H).length=139*(channels (2*H+1)).length+2 := by sorry

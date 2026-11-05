-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_BuiltO_transfer
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory.BuiltO.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:26:35.580293+00:00
-- url     : https://prove2.me/theorems/7011f925-3887-4dd1-a96e-b16754feb0f4
-- title:
--   transfer
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L264-L271
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L264-L271

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_transfer
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_transfer

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory.BuiltO.transfer {C : Config} {D : Data C} {μ ν ξ : ℕ → ℤ} {cutoff depth : ℕ}
    (G : AppendGuard C D lim depth μ) (H : BuiltO C D μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.Onew+C.nO≤cutoff) : BuiltO C D μ ξ := by sorry

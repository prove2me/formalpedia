-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_AppendGuard_runO
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:27:21.521017+00:00
-- url     : https://prove2.me/theorems/427eae81-844d-4d3e-8910-59e4268d909d
-- title:
--   runO
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L203-L224
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L203-L224

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runO {C : Config} {D : Data C} {depth : ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : BuiltC C D μ ν) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Omatrix,C.row,C.Oold,C.Onew,C.nO,C.J+2,C.p,C.power,C.hashWork] ν
      (LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO)
      (fun _ ξ => BuiltO C D μ ξ) := by sorry

-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSeedHeader_result_seg
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.result_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:35.899698+00:00
-- url     : https://prove2.me/theorems/6f9efeaa-ae25-4b2c-9472-b81d497470a3
-- title:
--   result_seg
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L22-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L22-L33

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.result_seg {μ : ℕ→ℤ} {xs : List ℤ} (X : Inputs) (H : Seg μ X.seed xs) :
    Seg (LightTernaryBudgetStep.changed
      (LightWeightedGlobalPrefixPrepare.seedChanged μ X.seed X.power X.liveHeader (X.j+1))
      (X.seed+41) X.p X.a X.b X.scale X.xB X.xC X.xP X.tB X.tC X.tP)
      X.seed (result xs X) := by sorry

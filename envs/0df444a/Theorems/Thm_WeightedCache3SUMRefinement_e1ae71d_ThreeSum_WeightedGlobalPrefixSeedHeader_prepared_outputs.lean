-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_outputs
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_outputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:51.430089+00:00
-- url     : https://prove2.me/theorems/f58ecfdd-48c8-4980-874b-142f190b809e
-- title:
--   prepared_outputs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L86-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L86-L112

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_outputs {X : Inputs} {μ ν : ℕ→ℤ}
    (H : Prepared X μ ν) (hhost : X.liveHeader+106≤X.seed)
    (hseed : X.seed+48≤X.prefixFree) :
    Seg ν (LightWeightedGlobalPrefixSetup.headerAt X.prefixFree X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.header X.m (X.j+1) X.F X.prefixFree
        (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))) ∧
    Seg ν X.prefixFree ((WeightedAddresses.codes (LightWeightedGlobalPrefixSetup.N X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.T X.m (X.j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
    LightSubsetAddress.Powers ν (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))
      (2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1)) := by sorry

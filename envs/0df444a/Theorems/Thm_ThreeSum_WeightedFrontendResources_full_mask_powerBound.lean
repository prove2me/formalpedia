-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrontendResources_full_mask_powerBound
-- name    : ThreeSum.WeightedFrontendResources.full_mask_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:45.78917+00:00
-- url     : https://prove2.me/theorems/c979ad51-1bb4-4b6d-8983-61a71375d972
-- title:
--   Weighted Frontend Resources: full mask power Bound
-- statement:
--   The Weighted Frontend Resources construction uses the full mask power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L390-L402
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L390-L402

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions

theorem ThreeSum.WeightedFrontendResources.full_mask_powerBound {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>4^TernaryLocalParameters.fixedLength (radixLength m n*m))
      (2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
-- name    : ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:23:00.361201+00:00
-- url     : https://prove2.me/theorems/83f44e40-7e55-43f3-a4d4-d9080cc3b5ec
-- title:
--   Weighted Global Frontend Resources: source Config config
-- statement:
--   The Weighted Global Frontend Resources construction uses the source Config config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L57-L60

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config (a N R A bank nb bv T h ws base stride tail group : ℕ) :
    LightWeightedWantedRowDispatch.sourceConfig (config a N R A bank nb bv T h ws)
      base stride tail group=
    config a N R A bank nb (base+group*stride+tail) T h ws := by sorry

attribute [defeq] ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config

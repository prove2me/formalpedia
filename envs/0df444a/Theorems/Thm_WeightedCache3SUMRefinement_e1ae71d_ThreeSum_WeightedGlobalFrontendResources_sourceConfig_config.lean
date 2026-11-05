-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:18:50.503496+00:00
-- url     : https://prove2.me/theorems/912cca95-663d-40df-9667-9773713890c6
-- title:
--   sourceConfig_config
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L57-L60

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config (a N R A bank nb bv T h ws base stride tail group : ℕ) :
    LightWeightedWantedRowDispatch.sourceConfig (config a N R A bank nb bv T h ws)
      base stride tail group=
    config a N R A bank nb (base+group*stride+tail) T h ws := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config

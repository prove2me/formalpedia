-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSetupResources_need_mono_prefix
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources.need_mono_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:24:35.695217+00:00
-- url     : https://prove2.me/theorems/3428a36c-4e6f-41bb-a918-05ce69088724
-- title:
--   need_mono_prefix
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L46-L55

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSetupResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources.need_mono_prefix {m j r F : ℕ} (hjr : j≤ r) :
    (need m j F).word≤ (need m r F).word ∧
    (need m j F).cells≤ (need m r F).cells ∧
    (need m j F).depth≤ (need m r F).depth := by sorry

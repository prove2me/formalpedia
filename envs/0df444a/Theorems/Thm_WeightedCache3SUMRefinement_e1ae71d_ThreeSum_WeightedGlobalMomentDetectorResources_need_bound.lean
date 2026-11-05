-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentDetectorResources_need_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources.need_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:29:48.140711+00:00
-- url     : https://prove2.me/theorems/dff772fd-b8bd-4a4d-b2f0-b3173a8f7b13
-- title:
--   need_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L45-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L45-L60

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_need_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources.need_bound (B U H : ℕ) :
    (need B U H).word≤coefficient B H*(U+1)^degree H ∧
    (need B U H).cells≤coefficient B H*(U+1)^degree H ∧
    (need B U H).depth≤coefficient B H*(U+1)^degree H := by sorry

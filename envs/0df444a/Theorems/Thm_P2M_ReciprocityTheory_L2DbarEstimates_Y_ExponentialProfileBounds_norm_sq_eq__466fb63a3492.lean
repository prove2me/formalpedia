-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_norm_sq_eq__466fb63a3492
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_norm_sq_eq__466fb63a3492
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:56.056423+00:00
-- url     : https://prove2.me/theorems/be28f795-7cbf-4753-8585-b2304d5833f7
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y Exponential Profile Bounds norm sq eq  466fb63a3492: P2 M Reciprocity Theory L2 Dbar Estimates Y Exponential Profile Bounds norm sq eq  466fb63a3492
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y Exponential Profile Bounds norm sq eq  466fb63a3492 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y Exponential Profile Bounds norm sq eq  466fb63a3492 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L74-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L74-L74

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
variable {n : ℕ}

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_norm_sq_eq__466fb63a3492 (y : V n) : ‖y‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«ExponentialProfileBounds».«norm_sq_eq'» := P2M_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_norm_sq_eq__466fb63a3492

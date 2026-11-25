-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_det_ne
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.det_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:18.249349+00:00
-- url     : https://prove2.me/theorems/c1766cdb-e6f2-5d4a-ab39-c63d21b1df65
-- title:
--   Exponential Profile Bounds: det ne
-- statement:
--   The Exponential Profile Bounds construction uses the det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L92-L98

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.det_ne (y : V n) :
    (fderiv ℂ ((atlas n).zLoc (w0I n) (sI n) ((atlas n).pick y))
      ((atlas n).chart ((atlas n).pick y) y)).det ≠ 0 := by sorry

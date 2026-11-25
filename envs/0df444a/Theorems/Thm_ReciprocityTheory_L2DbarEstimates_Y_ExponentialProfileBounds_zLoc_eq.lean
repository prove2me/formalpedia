-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_zLoc_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.zLoc_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:14.121415+00:00
-- url     : https://prove2.me/theorems/fd3aaad5-b1cd-4a4a-948f-c13547383adb
-- title:
--   Exponential Profile Bounds: z Loc eq
-- statement:
--   The Exponential Profile Bounds construction uses the z Loc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L88-L90

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.zLoc_eq (i : Unit) : (atlas n).zLoc (w0I n) (sI n) i = id := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_nsq_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.nsq_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:32.94391+00:00
-- url     : https://prove2.me/theorems/5d9a2754-b606-46ec-acc2-c9258caf241a
-- title:
--   Exponential Profile Bounds: nsq eq
-- statement:
--   The Exponential Profile Bounds construction uses the nsq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean#L50-L53

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.nsq_eq (f : Unit → V n → ℂ) (y : V n) :
    (atlas n).nsq 1 f y = ‖f () y‖ ^ 2 * (1 + ‖y‖ ^ 2)⁻¹ := by sorry

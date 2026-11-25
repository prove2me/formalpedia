-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sub_isBigO_of_det_ne_zero
-- name    : ReciprocityTheory.L2DbarEstimates.Y.sub_isBigO_of_det_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:21.98099+00:00
-- url     : https://prove2.me/theorems/ab6e13e1-82b2-41eb-bdc0-5cd21578a837
-- title:
--   Y: sub is Big O of det ne zero
-- statement:
--   The Y construction uses the sub is Big O of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L134-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L134-L150

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.sub_isBigO_of_det_ne_zero {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by sorry

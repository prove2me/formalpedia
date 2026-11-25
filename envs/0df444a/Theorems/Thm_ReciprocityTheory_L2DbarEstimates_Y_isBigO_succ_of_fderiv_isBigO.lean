-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isBigO_succ_of_fderiv_isBigO
-- name    : ReciprocityTheory.L2DbarEstimates.Y.isBigO_succ_of_fderiv_isBigO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:29.363702+00:00
-- url     : https://prove2.me/theorems/182cfb4d-85a0-46f9-969d-4997468b0c60
-- title:
--   Y: is Big O succ of fderiv is Big O
-- statement:
--   The Y construction uses the is Big O succ of fderiv is Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L21-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L21-L47

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.isBigO_succ_of_fderiv_isBigO {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (h0 : f x = 0) {m : ℕ}
    (hO : fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ m) :
    f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by sorry

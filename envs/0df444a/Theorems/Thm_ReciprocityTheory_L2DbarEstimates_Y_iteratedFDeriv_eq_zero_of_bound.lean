-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_iteratedFDeriv_eq_zero_of_bound
-- name    : ReciprocityTheory.L2DbarEstimates.Y.iteratedFDeriv_eq_zero_of_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:00.242541+00:00
-- url     : https://prove2.me/theorems/1232eba3-83cc-5187-b17a-9913ef2d0d94
-- title:
--   Y: iterated FDeriv eq zero of bound
-- statement:
--   The Y construction uses the iterated FDeriv eq zero of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L96-L106

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

theorem ReciprocityTheory.L2DbarEstimates.Y.iteratedFDeriv_eq_zero_of_bound {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (hO : ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1)) :
    ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0 := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bound_of_iteratedFDeriv_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bound_of_iteratedFDeriv_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:03.695462+00:00
-- url     : https://prove2.me/theorems/0123efbc-ca7d-4600-89e7-ce7eaf527f4d
-- title:
--   Y: bound of iterated FDeriv eq zero
-- statement:
--   The Y construction uses the bound of iterated FDeriv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L108-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L108-L115

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

theorem ReciprocityTheory.L2DbarEstimates.Y.bound_of_iteratedFDeriv_eq_zero {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (h : ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1) := by sorry

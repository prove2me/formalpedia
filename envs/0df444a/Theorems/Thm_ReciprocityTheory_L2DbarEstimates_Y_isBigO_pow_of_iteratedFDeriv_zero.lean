-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isBigO_pow_of_iteratedFDeriv_zero
-- name    : ReciprocityTheory.L2DbarEstimates.Y.isBigO_pow_of_iteratedFDeriv_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:04.961159+00:00
-- url     : https://prove2.me/theorems/9067d9f2-bd07-4e6b-acfc-3f752dc156bc
-- title:
--   Y: is Big O pow of iterated FDeriv zero
-- statement:
--   The Y construction uses the is Big O pow of iterated FDeriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean#L76-L94

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

theorem ReciprocityTheory.L2DbarEstimates.Y.isBigO_pow_of_iteratedFDeriv_zero {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (∀ k < m, iteratedFDeriv ℂ k f x = 0) →
    f =O[𝓝 x] fun v => ‖v - x‖ ^ m := by sorry

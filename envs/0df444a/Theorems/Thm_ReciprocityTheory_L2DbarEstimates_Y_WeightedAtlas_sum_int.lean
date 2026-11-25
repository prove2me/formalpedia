-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sum_int
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sum_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:43.852053+00:00
-- url     : https://prove2.me/theorems/7831b75a-43a6-41a9-9053-d0599cc86970
-- title:
--   Weighted Atlas: sum int
-- statement:
--   The Weighted Atlas construction uses the sum int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L156-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L156-L176

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sum_int (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (hh : ∀ q ∈ F, A.IsSec la (h q)) (Wt : Y → ℝ) (hWt : Measurable Wt)
    (hW0 : ∀ y, 0 ≤ Wt y)
    (hint : ∀ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ∂A.mu < ⊤ := by sorry

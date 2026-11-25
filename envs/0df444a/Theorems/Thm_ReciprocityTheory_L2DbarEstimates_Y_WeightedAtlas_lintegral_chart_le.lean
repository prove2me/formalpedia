-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_lintegral_chart_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.lintegral_chart_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:37.801064+00:00
-- url     : https://prove2.me/theorems/be7cb07a-31eb-505e-a9ac-24c537bd2cbf
-- title:
--   Weighted Atlas: lintegral chart le
-- statement:
--   The Weighted Atlas construction uses the lintegral chart le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L104-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L104-L164

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
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

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.lintegral_chart_le (A : WeightedAtlas n Y ι La) (i : ι) (y0 : Y) {W : Set (V n)}
    (hW : IsOpen W) (hWt : W ⊆ (A.chart i).target) (c : ℝ≥0∞)
    (hc : ∀ v ∈ W, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ c)
    (ψ : V n → ℝ≥0∞) (hψ : Continuous ψ) :
    ∫⁻ x in (A.chart i).source ∩ A.chart i ⁻¹' W, ψ (A.chart i x) ∂A.mu ≤
      c * ∫⁻ v in W, ψ v := by sorry

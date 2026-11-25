-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_q_cd
-- name    : ReciprocityTheory.L2DbarEstimates.Y.hyq_q_cd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:19:04.144301+00:00
-- url     : https://prove2.me/theorems/c2305bb0-e450-4ea4-8e36-0838038a3b3e
-- title:
--   Y: hyq q cd
-- statement:
--   The Y construction uses the hyq q cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L199-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L199-L215

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.hyq_q_cd (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    (∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) v) ∧
    ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)]
      fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) ∧
    (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) ≠ 0 := by sorry

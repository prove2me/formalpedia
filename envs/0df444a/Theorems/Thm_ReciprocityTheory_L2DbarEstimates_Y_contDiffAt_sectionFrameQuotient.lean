-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffAt_sectionFrameQuotient
-- name    : ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_sectionFrameQuotient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:52.8054+00:00
-- url     : https://prove2.me/theorems/5a971ab3-3f77-4ffd-9ec8-24fe0586421b
-- title:
--   Y: cont Diff At section Frame Quotient
-- statement:
--   The Y construction uses the cont Diff At section Frame Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L290-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L290-L314

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

theorem ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_sectionFrameQuotient (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) := by sorry

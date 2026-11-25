-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_det_diff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsB_det_diff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:49.978367+00:00
-- url     : https://prove2.me/theorems/323340fd-8e70-56f8-a46d-bdccb7af56fc
-- title:
--   Y: bs B det diff
-- statement:
--   The Y construction uses the bs B det diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L112-L120

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
variable {mu0 : La} {σ : ι → Y → ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.bsB_det_diff (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {x : Y}
    (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      DifferentiableAt ℂ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psiC_smooth
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsB_psiC_smooth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:56.745058+00:00
-- url     : https://prove2.me/theorems/0a542253-326c-4238-98d9-f9eed615ff21
-- title:
--   Y: bs B psi C smooth
-- statement:
--   The Y construction uses the bs B psi C smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L129-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L129-L152

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

theorem ReciprocityTheory.L2DbarEstimates.Y.bsB_psiC_smooth (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.ph (mu0 - A.kap) i ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) := by sorry

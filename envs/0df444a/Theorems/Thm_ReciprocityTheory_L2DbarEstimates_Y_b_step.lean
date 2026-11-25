-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_b_step
-- name    : ReciprocityTheory.L2DbarEstimates.Y.b_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T17:03:11.345396+00:00
-- url     : https://prove2.me/theorems/b3f8e37f-ee81-59d1-842c-382f1d983f0f
-- title:
--   Y: b step
-- statement:
--   The Y construction uses the b step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStep.lean#L14-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStep.lean#L14-L86

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.b_step {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
    (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) (hLSE : LSEAll.{u} n)
    (hn : 2 ≤ n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → ι → Y → ℂ,
      (∀ k, A.IsSec (mu0 + (T' - 1) • L) (hh k) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (hh k) y *
          A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ k, s k i y * hh k i y := by sorry

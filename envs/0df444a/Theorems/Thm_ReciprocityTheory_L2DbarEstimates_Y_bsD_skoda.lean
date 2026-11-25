-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_skoda
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsD_skoda
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:14.866461+00:00
-- url     : https://prove2.me/theorems/e1a17a8b-887c-4265-ab1c-dc02c58e76d3
-- title:
--   Y: bs D skoda
-- statement:
--   The Y construction uses the bs D skoda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L95-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L95-L133

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.bsD_skoda (hS : SAll.{u} n) (hLSE : LSEAll.{u} n) (hn : 2 ≤ n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → A.Mset w0 s De → ℂ, (∀ k, Holo n (flatStein A hD hF).z (hh k)) ∧
      (∀ x : A.Mset w0 s De, f (A.pick (x : Y)) x /
          (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T') =
        ∑ k, s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x * hh k x) ∧
      ∫⁻ x, ENNReal.ofReal ((∑ k, ‖hh k x‖ ^ 2) *
          (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤ := by sorry

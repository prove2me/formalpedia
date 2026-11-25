-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_heq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsD_heq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:35.9928+00:00
-- url     : https://prove2.me/theorems/cf9dab5f-d369-5c1e-9abd-be6ba47a5baa
-- title:
--   Y: bs D heq
-- statement:
--   The Y construction uses the bs D heq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L47-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L47-L74

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

theorem ReciprocityTheory.L2DbarEstimates.Y.bsD_heq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (f : ι → Y → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + T' • L) f x * A.sqn L s x ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w x ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2 + 1)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by sorry

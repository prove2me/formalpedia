-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_meas
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsE_meas
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:49:59.525458+00:00
-- url     : https://prove2.me/theorems/071d8798-1de0-4b87-bf12-719cb13135fa
-- title:
--   Y: bs E meas
-- statement:
--   The Y construction uses the bs E meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepE.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepE.lean#L86-L102

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
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
open Classical

theorem ReciprocityTheory.L2DbarEstimates.Y.bsE_meas (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h) :
    Measurable ((A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y * bsW A L w s T' y))
      (fun _ => 0)) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_pos
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsD_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:19.052532+00:00
-- url     : https://prove2.me/theorems/6a7a044b-670c-56a5-be23-ad34fdfe438a
-- title:
--   Y: bs D pos
-- statement:
--   The Y construction uses the bs D pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L17-L34

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
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

theorem ReciprocityTheory.L2DbarEstimates.Y.bsD_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (x : Y) (hx : x ∈ A.Mset w0 s De) :
    0 < A.nsq L w0 x ∧ 0 < A.nsq mu0 σ x ∧
      0 < ∑ k, ‖s k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      0 < ∑ k, ‖w k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      (jz A w0 s (A.pick x) x).det ≠ 0 := by sorry

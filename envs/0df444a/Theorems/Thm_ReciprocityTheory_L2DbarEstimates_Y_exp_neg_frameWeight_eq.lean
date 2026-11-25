-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_exp_neg_frameWeight_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.exp_neg_frameWeight_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:35.795268+00:00
-- url     : https://prove2.me/theorems/c09cfc08-92d9-4f1c-89a7-f627ba0b3b16
-- title:
--   Y: exp neg frame Weight eq
-- statement:
--   The Y construction uses the exp neg frame Weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepC.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepC.lean#L70-L87

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
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
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.exp_neg_frameWeight_eq {N : ℕ} (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (mu0 : La) (σ : ι → Y → ℂ) (y : Y) (hσ : 0 < A.nsq mu0 σ y)
    (hd : (jz A w0 s (A.pick y) y).det ≠ 0)
    (hS : 0 < ∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) :
    Real.exp (-bsPh0 A w w0 s mu0 σ y) =
      A.nsq mu0 σ y * (Real.exp (A.ph A.kap (A.pick y) y) / ‖(jz A w0 s (A.pick y) y).det‖ ^ 2) *
        (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by sorry

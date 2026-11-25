-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_holo_flat_iff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.holo_flat_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:09.467113+00:00
-- url     : https://prove2.me/theorems/efd41ec0-a02c-4182-81ef-3596577a0095
-- title:
--   Y: holo flat iff
-- statement:
--   The Y construction uses the holo flat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalc.lean#L16-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalc.lean#L16-L55

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
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

theorem ReciprocityTheory.L2DbarEstimates.Y.holo_flat_iff {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ) :
    Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) ↔
      ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by sorry

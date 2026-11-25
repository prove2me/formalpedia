-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_smoothR_flat
-- name    : ReciprocityTheory.L2DbarEstimates.Y.smoothR_flat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T16:09:27.362807+00:00
-- url     : https://prove2.me/theorems/0fcd1215-d18e-4f80-af0e-1b6737e6ebab
-- title:
--   Y: smooth R flat
-- statement:
--   The Y construction uses the smooth R flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L254-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L254-L262

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
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

theorem ReciprocityTheory.L2DbarEstimates.Y.smoothR_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (φ : Y → ℝ)
    (hφ : ∀ x ∈ A.Mset w0 s De, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) :
    SmoothR n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) := by sorry

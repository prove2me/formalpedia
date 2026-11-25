-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_add
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviAt_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:25.823575+00:00
-- url     : https://prove2.me/theorems/147226f9-4638-4e85-847f-d8007a9710a5
-- title:
--   Y: levi At add
-- statement:
--   The Y construction uses the levi At add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L432-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L432-L456

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

theorem ReciprocityTheory.L2DbarEstimates.Y.leviAt_add {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y)
    (hf : ContDiffAt ℝ 2 (f ∘ (A.chart i).symm) (A.chart i y))
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart i).symm) (A.chart i y)) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => f x + g x) y ξ = A.leviAt i f y ξ + A.leviAt i g y ξ := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_congr
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviAt_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:38.297835+00:00
-- url     : https://prove2.me/theorems/7cd57953-bf4b-5ec6-843e-d6df47e13584
-- title:
--   Y: levi At congr
-- statement:
--   The Y construction uses the levi At congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L421-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L421-L430

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

theorem ReciprocityTheory.L2DbarEstimates.Y.leviAt_congr {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y) (hy : y ∈ (A.chart i).source)
    (h : f =ᶠ[𝓝 y] g) (ξ : Fin n → ℂ) : A.leviAt i f y ξ = A.leviAt i g y ξ := by sorry

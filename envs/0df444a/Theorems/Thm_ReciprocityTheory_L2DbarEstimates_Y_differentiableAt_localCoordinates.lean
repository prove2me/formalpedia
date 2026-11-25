-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_differentiableAt_localCoordinates
-- name    : ReciprocityTheory.L2DbarEstimates.Y.differentiableAt_localCoordinates
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:46.689799+00:00
-- url     : https://prove2.me/theorems/66bf053a-72dd-4ea8-bc79-bd8ff9c20c23
-- title:
--   Y: differentiable At local Coordinates
-- statement:
--   The Y construction uses the differentiable At local Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L157-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L157-L173

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.differentiableAt_localCoordinates (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by sorry

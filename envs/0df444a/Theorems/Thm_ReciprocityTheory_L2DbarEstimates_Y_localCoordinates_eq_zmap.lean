-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_localCoordinates_eq_zmap
-- name    : ReciprocityTheory.L2DbarEstimates.Y.localCoordinates_eq_zmap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:58.244193+00:00
-- url     : https://prove2.me/theorems/751dd7a9-98c0-5e2c-9f69-4a5e2505f63a
-- title:
--   Y: local Coordinates eq zmap
-- statement:
--   The Y construction uses the local Coordinates eq zmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L101-L110

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

theorem ReciprocityTheory.L2DbarEstimates.Y.localCoordinates_eq_zmap (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by sorry

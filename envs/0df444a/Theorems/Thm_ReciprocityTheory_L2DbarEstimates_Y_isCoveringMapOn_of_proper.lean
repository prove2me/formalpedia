-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isCoveringMapOn_of_proper
-- name    : ReciprocityTheory.L2DbarEstimates.Y.isCoveringMapOn_of_proper
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:31.076141+00:00
-- url     : https://prove2.me/theorems/f97e8bab-68e8-4cb6-bda7-33cf67a34b4e
-- title:
--   Y: is Covering Map On of proper
-- statement:
--   The Y construction uses the is Covering Map On of proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L12-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L12-L53

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

theorem ReciprocityTheory.L2DbarEstimates.Y.isCoveringMapOn_of_proper {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by sorry

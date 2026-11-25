-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_holo_restrict_open
-- name    : ReciprocityTheory.L2DbarEstimates.Y.holo_restrict_open
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:51.183113+00:00
-- url     : https://prove2.me/theorems/a99101ff-4a43-4908-bb66-f081b99c7bb7
-- title:
--   Y: holo restrict open
-- statement:
--   The Y construction uses the holo restrict open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L114-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L114-L132

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

theorem ReciprocityTheory.L2DbarEstimates.Y.holo_restrict_open {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by sorry

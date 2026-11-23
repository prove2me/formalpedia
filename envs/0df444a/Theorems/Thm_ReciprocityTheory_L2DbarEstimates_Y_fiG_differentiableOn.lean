-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiG_differentiableOn
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fiG_differentiableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:45.857671+00:00
-- url     : https://prove2.me/theorems/a73d9fe6-f414-46f6-ae95-f0ddbcc1a181
-- title:
--   Y: fi G differentiable On
-- statement:
--   The Y construction uses the fi G differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourIndep.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourIndep.lean#L42-L48

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.fiG_differentiableOn {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube f Ω)) (ν : Fin f → ℤ) :
    DifferentiableOn ℂ (fiG h ν) (tube f Ω) := by sorry

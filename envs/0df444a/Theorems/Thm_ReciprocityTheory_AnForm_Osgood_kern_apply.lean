-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_kern_apply
-- name    : ReciprocityTheory.AnForm.Osgood.kern_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:31.409221+00:00
-- url     : https://prove2.me/theorems/5de6e738-c9a4-4bab-8199-8da055754177
-- title:
--   Osgood: kern apply
-- statement:
--   The Osgood construction uses the kern apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L63-L68

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.Osgood.kern_apply {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (θ : Cube n) :
    kern c r z θ = ∏ i, (torusMap c (fun _ => r) θ.1 i - z i)⁻¹ := by sorry

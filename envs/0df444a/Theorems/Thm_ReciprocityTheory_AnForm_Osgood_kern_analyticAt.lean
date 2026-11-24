-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_kern_analyticAt
-- name    : ReciprocityTheory.AnForm.Osgood.kern_analyticAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:28.393141+00:00
-- url     : https://prove2.me/theorems/63b23448-a3ac-4253-9701-8f1d3ccb8098
-- title:
--   Osgood: kern analytic At
-- statement:
--   The Osgood construction uses the kern analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L70-L82

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

theorem ReciprocityTheory.AnForm.Osgood.kern_analyticAt (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ (kern c r) c := by sorry

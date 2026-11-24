-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_fctlCLM_kern
-- name    : ReciprocityTheory.AnForm.Osgood.fctlCLM_kern
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:33.46194+00:00
-- url     : https://prove2.me/theorems/6b36f26a-e9dc-452c-83bb-119e2a21dbc3
-- title:
--   Osgood: fctl CLM kern
-- statement:
--   The Osgood construction uses the fctl CLM kern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean#L126-L135

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

theorem ReciprocityTheory.AnForm.Osgood.fctlCLM_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    fctlCLM c hr f hf (kern c r z) = (2 * π * I) ^ n * f z := by sorry

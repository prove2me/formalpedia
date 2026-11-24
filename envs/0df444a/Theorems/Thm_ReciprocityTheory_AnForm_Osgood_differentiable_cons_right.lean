-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_right
-- name    : ReciprocityTheory.AnForm.Osgood.differentiable_cons_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:43.215887+00:00
-- url     : https://prove2.me/theorems/b48370bb-c5cc-4e1a-81d8-5e810fb071b3
-- title:
--   Osgood: differentiable cons right
-- statement:
--   The Osgood construction uses the differentiable cons right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L11-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
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

theorem ReciprocityTheory.AnForm.Osgood.differentiable_cons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by sorry

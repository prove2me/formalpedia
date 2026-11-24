-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_left
-- name    : ReciprocityTheory.AnForm.Osgood.differentiable_cons_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:32.149935+00:00
-- url     : https://prove2.me/theorems/41c5e936-d21e-41a8-9313-d90cc5d939f7
-- title:
--   Osgood: differentiable cons left
-- statement:
--   The Osgood construction uses the differentiable cons left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L20-L27

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

theorem ReciprocityTheory.AnForm.Osgood.differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by sorry

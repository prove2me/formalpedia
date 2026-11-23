-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap
-- name    : ReciprocityTheory.AnForm.Osgood.continuous_torusMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:05.643518+00:00
-- url     : https://prove2.me/theorems/b8206f93-34f3-46f0-b5fb-d2ad7556fb52
-- title:
--   Osgood: continuous torus Map
-- statement:
--   The Osgood construction uses the continuous torus Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L64-L68

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

theorem ReciprocityTheory.AnForm.Osgood.continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by sorry

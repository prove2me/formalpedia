-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_sub_ne
-- name    : ReciprocityTheory.AnForm.Osgood.torusMap_sub_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:16.655087+00:00
-- url     : https://prove2.me/theorems/6f1aaf62-fd76-4ad7-ab98-dd7f5fc730ba
-- title:
--   Osgood: torus Map sub ne
-- statement:
--   The Osgood construction uses the torus Map sub ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L54-L62

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

theorem ReciprocityTheory.AnForm.Osgood.torusMap_sub_ne {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by sorry

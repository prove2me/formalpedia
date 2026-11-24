-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_mem_closedBall
-- name    : ReciprocityTheory.AnForm.Osgood.torusMap_mem_closedBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:43.311161+00:00
-- url     : https://prove2.me/theorems/649bc34b-e368-476e-a39d-d0ef622e35d9
-- title:
--   Osgood: torus Map mem closed Ball
-- statement:
--   The Osgood construction uses the torus Map mem closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L48-L52

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

theorem ReciprocityTheory.AnForm.Osgood.torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by sorry

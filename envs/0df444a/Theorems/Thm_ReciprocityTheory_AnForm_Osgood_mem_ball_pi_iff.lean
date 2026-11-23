-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff
-- name    : ReciprocityTheory.AnForm.Osgood.mem_ball_pi_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:27.207844+00:00
-- url     : https://prove2.me/theorems/ad83fa03-c727-4b76-82ba-7b8192d935d7
-- title:
--   Osgood: mem ball pi iff
-- statement:
--   The Osgood construction uses the mem ball pi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/OsgoodA.lean#L33-L35

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

theorem ReciprocityTheory.AnForm.Osgood.mem_ball_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by sorry

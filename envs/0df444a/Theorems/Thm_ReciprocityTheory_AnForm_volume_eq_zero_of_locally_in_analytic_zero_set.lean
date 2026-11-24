-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_volume_eq_zero_of_locally_in_analytic_zero_set
-- name    : ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:46.43013+00:00
-- url     : https://prove2.me/theorems/2a93a918-d4ec-4344-beea-8105c23c9e06
-- title:
--   An Form: volume eq zero of locally in analytic zero set
-- statement:
--   The An Form construction uses the volume eq zero of locally in analytic zero set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/NullZero.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/NullZero.lean#L139-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Metric Filter Topology
open MeasureTheory Metric Filter Topology

theorem ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set {D : ℕ} (S : Set (Fin D → ℂ))
    (h : ∀ z ∈ S, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ S ∩ W, f w = 0) :
    volume S = 0 := by sorry

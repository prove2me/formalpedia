-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_volume_zero_set_of_analyticOnNhd
-- name    : ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:12.595929+00:00
-- url     : https://prove2.me/theorems/8c1db8f0-add4-4b7e-94ba-320017ddc169
-- title:
--   An Form: volume zero set of analytic On Nhd
-- statement:
--   The An Form construction uses the volume zero set of analytic On Nhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/NullZero.lean#L121-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/NullZero.lean#L121-L137

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

theorem ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hc : IsPreconnected U) {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) :
    volume {z | z ∈ U ∧ f z = 0} = 0 := by sorry

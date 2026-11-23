-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_exists_chart_partition
-- name    : ReciprocityTheory.AnForm.exists_chart_partition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:59.179271+00:00
-- url     : https://prove2.me/theorems/f98141ab-d0d3-4460-9e64-e2d7c92bf6cc
-- title:
--   An Form: exists chart partition
-- statement:
--   The An Form construction uses the exists chart partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Partition.lean#L8-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Partition.lean#L8-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open scoped ContDiff
open Set Metric

theorem ReciprocityTheory.AnForm.exists_chart_partition {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {D m : ℕ} (e : Fin m → OpenPartialHomeomorph X (Fin D → ℂ))
    (hcov : ∀ x, ∃ i, x ∈ (e i).source)
    (htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) :
    ∃ χ : Fin m → X → ℝ, (∀ i x, 0 ≤ χ i x) ∧ (∀ x, ∑ i, χ i x = 1) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source) ∧
      (∀ i j, ContDiffOn ℝ ∞ (χ i ∘ (e j).symm) (e j).target) := by sorry

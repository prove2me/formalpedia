-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_exists_diag
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.exists_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:20.387543+00:00
-- url     : https://prove2.me/theorems/55ea509b-4d1c-456e-85d0-6d03fb07342d
-- title:
--   Laplace: exists diag
-- statement:
--   The Laplace construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L87-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L87-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.exists_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    ∃ (L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) (b : Fin (Module.finrank ℝ E) → ℂ),
      (∀ i, 0 < (b i).re) ∧ ∀ w, B (L w) (L w) = ∑ i, b i * (w i : ℂ) ^ 2 := by sorry

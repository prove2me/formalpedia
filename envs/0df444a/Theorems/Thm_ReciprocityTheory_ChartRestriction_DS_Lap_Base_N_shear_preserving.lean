-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_shear_preserving
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.shear_preserving
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:19.168533+00:00
-- url     : https://prove2.me/theorems/617c505d-d430-4191-9ba8-7c0e8546e4d0
-- title:
--   N: shear preserving
-- statement:
--   The N construction uses the shear preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L71-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L71-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.shear_preserving (μ : Measure E) [μ.IsAddHaarMeasure] (G : ℕ → Submodule ℝ E) (L : ℕ)
    (hG0 : G 0 = ⊤) (hL : G L = ⊥) (Φ : E → E) (hΦ : Differentiable ℝ Φ)
    (hbij : Function.Bijective Φ)
    (hsh : ∀ j x y, x - y ∈ G j → Φ x - Φ y - (x - y) ∈ G (j + 1)) : MeasurePreserving Φ μ μ := by sorry

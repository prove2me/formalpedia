-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_growth
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.iter_growth
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:37.461+00:00
-- url     : https://prove2.me/theorems/848614b3-ba12-5d1c-805c-20a81caeaf43
-- title:
--   Is Shear: iter growth
-- statement:
--   The Is Shear construction uses the iter growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L229-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L229-L271

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
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.iter_growth (hf : IsShear F f) {Cf : ℝ} {Mf : ℕ} (hCf : 0 ≤ Cf)
    (hb : ∀ x ∈ F 0, ‖f x‖ ≤ Cf * ‖x‖ * (1 + ‖x‖) ^ Mf) (i : ℕ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ z ∈ F 0, ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M := by sorry

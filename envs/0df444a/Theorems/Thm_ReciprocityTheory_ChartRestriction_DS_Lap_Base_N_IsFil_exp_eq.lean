-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsFil.exp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:43.389279+00:00
-- url     : https://prove2.me/theorems/6cdd7045-4117-427a-90db-dc725642ed95
-- title:
--   Is Fil: exp eq
-- statement:
--   The Is Fil construction uses the exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L304-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L304-L321

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsFil.exp_eq (hF : IsFil F L) {x : A} (hx : x ∈ F 0) :
    NormedSpace.exp x = 1 + (x + ∑ k ∈ range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)) := by sorry

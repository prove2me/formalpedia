-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_mem_grpN
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_mem_grpN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:20.303703+00:00
-- url     : https://prove2.me/theorems/7300a0fa-3cf3-48e9-b448-d54b7cebadb8
-- title:
--   N: exp mem grp N
-- statement:
--   The N construction uses the exp mem grp N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L445-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L445-L451

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
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_mem_grpN (hF : IsFil F L) (hst : IsAdj F st) {Y : A} (hY : Y ∈ lieN F st) :
    NormedSpace.exp Y ∈ grpN F st := by sorry

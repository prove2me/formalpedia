-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_chart_haar
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_haar
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:24.427932+00:00
-- url     : https://prove2.me/theorems/fa095d4e-380c-52ee-9265-94a44ec1f664
-- title:
--   N: exp chart haar
-- statement:
--   The N construction uses the exp chart haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L636-L665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L636-L665

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
variable [FiniteDimensional ℝ A] {st : A →ₗ[ℝ] A} [MeasurableSpace A] [BorelSpace A]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_haar (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] :
    let ν := μ.map (fun Y : lieN F st => NormedSpace.exp (Y : A))
    SigmaFinite ν ∧ ν ≠ 0 ∧ ν {x | x ∉ grpN F st} = 0 ∧ ∀ s ∈ grpN F st, ν.map (s * ·) = ν := by sorry

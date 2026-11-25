-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_chart_invariant
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_invariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:44.909643+00:00
-- url     : https://prove2.me/theorems/09c60b92-1d8d-56d7-8c04-fc14cc1fbf70
-- title:
--   N: exp chart invariant
-- statement:
--   The N construction uses the exp chart invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L497-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L497-L615

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_invariant (hF : IsFil F L) (hst : IsAdj F st)
    [MeasurableSpace (lieN F st)] [BorelSpace (lieN F st)] (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] {s : A} (hs : s ∈ grpN F st) :
    ∃ Φ : lieN F st → lieN F st, MeasurePreserving Φ μ μ ∧
      ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A) := by sorry

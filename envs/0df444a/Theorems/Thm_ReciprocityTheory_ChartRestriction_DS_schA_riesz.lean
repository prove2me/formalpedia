-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_schA_riesz
-- name    : ReciprocityTheory.ChartRestriction.DS.schA_riesz
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:11.640825+00:00
-- url     : https://prove2.me/theorems/08dd0739-0898-4bfc-ba8b-bdb0cdf7fda0
-- title:
--   DS: sch A riesz
-- statement:
--   The DS construction uses the sch A riesz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/SchurA.lean#L31-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/SchurA.lean#L31-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_SchurA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.schA_riesz (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) (T : Submodule ℂ M) (hT : T ≤ genSub E V)
    (hTk : IsKStableSub ε E T) (f : M →ₗ[ℂ] ℂ) (μ : Fin n → ℝ)
    (hfd : ∀ a, ∀ y ∈ T, f (E a a y) = (μ a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y ∈ T, f (E b a y) = 0) {y₀ : M} (hy₀ : y₀ ∈ T) :
    ∃ u ∈ T, IsKHWVec ε E μ u ∧ inner ℂ u y₀ = f y₀ ∧ ∀ v ∈ T ⊓ V, inner ℂ u v = f v := by sorry

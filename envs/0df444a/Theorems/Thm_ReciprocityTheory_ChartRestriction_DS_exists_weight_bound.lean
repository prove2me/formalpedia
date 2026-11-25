-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_weight_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_weight_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:22.726265+00:00
-- url     : https://prove2.me/theorems/a2d3466f-7f0d-5d2b-bd6f-7a2025d65f5f
-- title:
--   DS: exists weight bound
-- statement:
--   The DS construction uses the exists weight bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L32-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L32-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.exists_weight_bound (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R := by sorry

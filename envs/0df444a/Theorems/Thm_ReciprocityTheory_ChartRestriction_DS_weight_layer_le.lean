-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_weight_layer_le
-- name    : ReciprocityTheory.ChartRestriction.DS.weight_layer_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:11.648066+00:00
-- url     : https://prove2.me/theorems/747a54bd-65b2-4dd8-8c6d-f0134af7c7e4
-- title:
--   DS: weight layer le
-- statement:
--   The DS construction uses the weight layer le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L99-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L99-L157

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

theorem ReciprocityTheory.ChartRestriction.DS.weight_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) {R : ℝ}
    (hR : ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R)
    (k : ℕ) {w : M} (hw : w ∈ layer ε E V k) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, E a a w = (μ a : ℂ) • w) :
    √(nsq (μ + rhoC ε)) ≤ R + √2 * k := by sorry

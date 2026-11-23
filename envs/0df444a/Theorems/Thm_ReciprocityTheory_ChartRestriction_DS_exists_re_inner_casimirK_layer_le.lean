-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_re_inner_casimirK_layer_le
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_re_inner_casimirK_layer_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:47.545791+00:00
-- url     : https://prove2.me/theorems/7f47d386-b05d-47eb-a797-f842c2a695f0
-- title:
--   DS: exists re inner casimir K layer le
-- statement:
--   The DS construction uses the exists re inner casimir K layer le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L159-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L159-L176

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

theorem ReciprocityTheory.ChartRestriction.DS.exists_re_inner_casimirK_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      RCLike.re (inner ℂ (casimirK ε E x) x) ≤ ((R + √2 * k) ^ 2 - nsq (rhoC ε)) * ‖x‖ ^ 2 := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lift_layer
-- name    : ReciprocityTheory.ChartRestriction.DS.lift_layer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:12.460526+00:00
-- url     : https://prove2.me/theorems/d3c95efc-5a3f-48f7-b177-8e250210cee2
-- title:
--   DS: lift layer
-- statement:
--   The DS construction uses the lift layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerWeight.lean#L19-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerWeight.lean#L19-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.lift_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V (k + 1))
    (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0) {μ : Fin n → ℝ} (hμ : IsKHWVec ε E μ w)
    (hw0 : w ≠ 0) :
    ∃ P ∈ ncV ε V (k + 1), P ≠ 0 ∧ IsKHWVec ε (bAct E (k + 1)) μ P ∧
      ∀ F ∈ ncV ε V (k + 1), phi E (k + 1) F ∈ layer ε E V k → inner ℂ F P = 0 := by sorry

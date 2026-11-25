-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_raise
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWord_raise
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:05.61095+00:00
-- url     : https://prove2.me/theorems/c5a2d730-7fdc-5be2-ba52-f15b25df8e6b
-- title:
--   DS: low Word raise
-- statement:
--   The DS construction uses the low Word raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L92-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L92-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.lowWord_raise (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  := by sorry

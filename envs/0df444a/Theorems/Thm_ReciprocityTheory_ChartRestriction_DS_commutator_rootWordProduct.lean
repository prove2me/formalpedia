-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_rootWordProduct
-- name    : ReciprocityTheory.ChartRestriction.DS.commutator_rootWordProduct
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:16.465301+00:00
-- url     : https://prove2.me/theorems/e7f64eac-b0da-4644-b96e-52b891ff3509
-- title:
--   DS: commutator root Word Product
-- statement:
--   The DS construction uses the commutator root Word Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L58-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L58-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
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

theorem ReciprocityTheory.ChartRestriction.DS.commutator_rootWordProduct (hE : IsGlRep E) (a b : Fin n) : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    E a b * word E κ - word E κ * E a b =
      ∑ i, ((if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) else 0) -
        (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) else 0))
  := by sorry

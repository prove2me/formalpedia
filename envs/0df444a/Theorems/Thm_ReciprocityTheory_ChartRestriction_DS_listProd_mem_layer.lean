-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_listProd_mem_layer
-- name    : ReciprocityTheory.ChartRestriction.DS.listProd_mem_layer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:54.255234+00:00
-- url     : https://prove2.me/theorems/436db897-a39c-5f43-9497-fca0b6bc330b
-- title:
--   DS: list Prod mem layer
-- statement:
--   The DS construction uses the list Prod mem layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L50-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
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

theorem ReciprocityTheory.ChartRestriction.DS.listProd_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    (l : List (Fin n × Fin n)) {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) :
    (l.map fun p => E p.1 p.2).prod v ∈ layer ε E V (j + l.length) := by sorry

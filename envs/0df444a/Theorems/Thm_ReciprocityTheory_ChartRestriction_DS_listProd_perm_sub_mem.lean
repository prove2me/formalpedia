-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_listProd_perm_sub_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.listProd_perm_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:56.612525+00:00
-- url     : https://prove2.me/theorems/b89bac7b-1c20-5937-9258-17481eb0f39a
-- title:
--   DS: list Prod perm sub mem
-- statement:
--   The DS construction uses the list Prod perm sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L59-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L59-L97

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

theorem ReciprocityTheory.ChartRestriction.DS.listProd_perm_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) (hnc : ∀ p ∈ l₁, ε p.1 ≠ ε p.2)
    {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) (m : ℕ) (hm : l₁.length ≤ m + 1) :
    (l₁.map fun p => E p.1 p.2).prod v - (l₂.map fun p => E p.1 p.2).prod v ∈
      layer ε E V (j + m) := by sorry

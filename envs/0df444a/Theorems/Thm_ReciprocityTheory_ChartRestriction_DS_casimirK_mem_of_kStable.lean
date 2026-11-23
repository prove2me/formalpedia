-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_mem_of_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.casimirK_mem_of_kStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:32.209113+00:00
-- url     : https://prove2.me/theorems/165d72e0-4f3c-4088-837b-7d5c0da48fe4
-- title:
--   DS: casimir K mem of k Stable
-- statement:
--   The DS construction uses the casimir K mem of k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L73-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.casimirK_mem_of_kStable {S : Submodule ℂ X} (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) : casimirK ε A x ∈ S := by sorry

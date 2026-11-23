-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_ncV_iff_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.mem_ncV_iff_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:54.176106+00:00
-- url     : https://prove2.me/theorems/cf8f269c-b294-4cdb-9115-449602c672d6
-- title:
--   DS: mem nc V iff apply
-- statement:
--   The DS construction uses the mem nc V iff apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L16-L20

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

theorem ReciprocityTheory.ChartRestriction.DS.mem_ncV_iff_apply {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by sorry

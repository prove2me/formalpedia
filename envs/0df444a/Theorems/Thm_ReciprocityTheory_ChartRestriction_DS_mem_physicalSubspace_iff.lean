-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_physicalSubspace_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.mem_physicalSubspace_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:22.535541+00:00
-- url     : https://prove2.me/theorems/a508c2bf-071c-505f-8543-01bafd4ab983
-- title:
--   DS: mem physical Subspace iff
-- statement:
--   The DS construction uses the mem physical Subspace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L32-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem ReciprocityTheory.ChartRestriction.DS.mem_physicalSubspace_iff (ε : Fin n → Bool) (x : TensorProduct ℂ N (Fock n)) :
    x ∈ physicalSubspace (N := N) ε ↔ ∀ j b, ¬(ε j = true ∧ ε b = false) → cmT j b x = 0 := by sorry

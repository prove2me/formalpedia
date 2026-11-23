-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_noncompactLayer_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.apply_mem_noncompactLayer_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:28.35594+00:00
-- url     : https://prove2.me/theorems/498fe5e2-dc98-48b1-a9c8-9f43097bf2d8
-- title:
--   DS: apply mem noncompact Layer succ
-- statement:
--   The DS construction uses the apply mem noncompact Layer succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L154-L160

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

theorem ReciprocityTheory.ChartRestriction.DS.apply_mem_noncompactLayer_succ {k : ℕ} {a b : Fin n} (hab : ε a ≠ ε b) {w : M}
    (hw : w ∈ layer ε E V k) : E a b w ∈ layer ε E V (k + 1) := by sorry

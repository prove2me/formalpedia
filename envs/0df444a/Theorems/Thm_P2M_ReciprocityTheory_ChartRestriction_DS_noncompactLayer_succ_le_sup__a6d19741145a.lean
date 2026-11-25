-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:39.064355+00:00
-- url     : https://prove2.me/theorems/56e4f243-e5fc-5c55-9b3e-6e2641c65895
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS noncompact Layer succ le sup  a6d19741145a: P2 M Reciprocity Theory Chart Restriction DS noncompact Layer succ le sup  a6d19741145a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS noncompact Layer succ le sup  a6d19741145a construction uses the P2 M Reciprocity Theory Chart Restriction DS noncompact Layer succ le sup  a6d19741145a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L274-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L274-L277

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a (k : ℕ) :
    layer ε E V (k + 1) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«noncompactLayer_succ_le_sup'» := P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a

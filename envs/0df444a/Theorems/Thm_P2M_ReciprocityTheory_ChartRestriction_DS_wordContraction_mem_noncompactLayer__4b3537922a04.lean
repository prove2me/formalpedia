-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_wordContraction_mem_noncompactLayer__4b3537922a04
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_wordContraction_mem_noncompactLayer__4b3537922a04
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:46.26098+00:00
-- url     : https://prove2.me/theorems/ef57df95-732b-517d-9935-4c08d1411db5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS word Contraction mem noncompact Layer  4b3537922a04: P2 M Reciprocity Theory Chart Restriction DS word Contraction mem noncompact Layer  4b3537922a04
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS word Contraction mem noncompact Layer  4b3537922a04 construction uses the P2 M Reciprocity Theory Chart Restriction DS word Contraction mem noncompact Layer  4b3537922a04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L180-L189

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_wordContraction_mem_noncompactLayer__4b3537922a04 {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) :
    phi E k F ∈ layer ε E V k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«wordContraction_mem_noncompactLayer'» := P2M_ReciprocityTheory_ChartRestriction_DS_wordContraction_mem_noncompactLayer__4b3537922a04

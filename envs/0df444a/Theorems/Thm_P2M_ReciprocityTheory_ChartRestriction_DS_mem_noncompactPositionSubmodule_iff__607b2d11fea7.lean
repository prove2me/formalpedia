-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:26.541237+00:00
-- url     : https://prove2.me/theorems/ad5717ed-6016-4cc2-91b1-2a2fb218bb82
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS mem noncompact Position Submodule iff  607b2d11fea7: P2 M Reciprocity Theory Chart Restriction DS mem noncompact Position Submodule iff  607b2d11fea7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS mem noncompact Position Submodule iff  607b2d11fea7 construction uses the P2 M Reciprocity Theory Chart Restriction DS mem noncompact Position Submodule iff  607b2d11fea7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L174-L178

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7 {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ, F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«mem_noncompactPositionSubmodule_iff'» := P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7

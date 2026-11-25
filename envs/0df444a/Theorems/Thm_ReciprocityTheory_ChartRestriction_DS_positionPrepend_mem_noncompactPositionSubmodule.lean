-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_positionPrepend_mem_noncompactPositionSubmodule
-- name    : ReciprocityTheory.ChartRestriction.DS.positionPrepend_mem_noncompactPositionSubmodule
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:00.350717+00:00
-- url     : https://prove2.me/theorems/348d65ab-9f4f-570a-80bf-e3b477720017
-- title:
--   DS: position Prepend mem noncompact Position Submodule
-- statement:
--   The DS construction uses the position Prepend mem noncompact Position Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L218-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L218-L241

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

theorem ReciprocityTheory.ChartRestriction.DS.positionPrepend_mem_noncompactPositionSubmodule {k : ℕ} {p : Fin n × Fin n} (hp : ε p.1 ≠ ε p.2) {G : Big n k M}
    (hG : G ∈ ncV ε V k) : indexPairPrepend p G ∈ ncV ε V (k + 1) := by sorry

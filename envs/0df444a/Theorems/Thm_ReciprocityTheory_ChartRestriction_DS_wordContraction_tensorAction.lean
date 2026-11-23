-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_tensorAction
-- name    : ReciprocityTheory.ChartRestriction.DS.wordContraction_tensorAction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:18.911061+00:00
-- url     : https://prove2.me/theorems/73d64dce-e053-4feb-a28c-6f6495417b35
-- title:
--   DS: word Contraction tensor Action
-- statement:
--   The DS construction uses the word Contraction tensor Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L116-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L116-L152

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

theorem ReciprocityTheory.ChartRestriction.DS.wordContraction_tensorAction (hE : IsGlRep E) (k : ℕ) (a b : Fin n) (F : Big n k M) :
    phi E k (bAct E k a b F) = E a b (phi E k F) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_genSub_eq_iSup_layer
-- name    : ReciprocityTheory.ChartRestriction.DS.genSub_eq_iSup_layer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:11.244154+00:00
-- url     : https://prove2.me/theorems/b0cc1d83-2610-4dcb-bf5a-9899efcc2b05
-- title:
--   DS: gen Sub eq i Sup layer
-- statement:
--   The DS construction uses the gen Sub eq i Sup layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L86-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.genSub_eq_iSup_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V) :
    genSub E V = ⨆ k, layer ε E V k := by sorry

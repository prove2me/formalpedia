-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TopExt__Multi_eq_zero_of_mem_span_6d6103b93336
-- name    : P2M_GlobalTheory_TopExt__Multi_eq_zero_of_mem_span_6d6103b93336
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:12.951482+00:00
-- url     : https://prove2.me/theorems/30f54dc9-4f19-4065-b61b-9edd297969b9
-- title:
--   P2 M Global Theory Top Ext  Multi eq zero of mem span 6d6103b93336: P2 M Global Theory Top Ext  Multi eq zero of mem span 6d6103b93336
-- statement:
--   The P2 M Global Theory Top Ext  Multi eq zero of mem span 6d6103b93336 construction uses the P2 M Global Theory Top Ext  Multi eq zero of mem span 6d6103b93336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L76-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

theorem P2M_GlobalTheory_TopExt__Multi_eq_zero_of_mem_span_6d6103b93336 {r n : ℕ} (hn : r < n) (v : Fin r → F) (w : Fin n → F)
    (hw : ∀ k, w k ∈ Submodule.span R (Set.range v)) : exteriorPower.ιMulti R n w = 0 := by sorry

alias «GlobalTheory».«TopExt».«ιMulti_eq_zero_of_mem_span» := P2M_GlobalTheory_TopExt__Multi_eq_zero_of_mem_span_6d6103b93336

-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TopExt_mul__Multi_congr_3a4c7c8aee3c
-- name    : P2M_GlobalTheory_TopExt_mul__Multi_congr_3a4c7c8aee3c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:10.031315+00:00
-- url     : https://prove2.me/theorems/2247bf6f-2a1c-4196-b83a-7deda5a8e390
-- title:
--   P2 M Global Theory Top Ext mul  Multi congr 3a4c7c8aee3c: P2 M Global Theory Top Ext mul  Multi congr 3a4c7c8aee3c
-- statement:
--   The P2 M Global Theory Top Ext mul  Multi congr 3a4c7c8aee3c construction uses the P2 M Global Theory Top Ext mul  Multi congr 3a4c7c8aee3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L60-L74

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

theorem P2M_GlobalTheory_TopExt_mul__Multi_congr_3a4c7c8aee3c (i : F →ₗ[R] H) {b : ℕ} (x : ExteriorAlgebra R H)
    (hx : ∀ f, x * ExteriorAlgebra.ι R (i f) = 0) (h h' : Fin b → H)
    (hh : ∀ k, h k - h' k ∈ LinearMap.range i) :
    x * ExteriorAlgebra.ιMulti R b h = x * ExteriorAlgebra.ιMulti R b h' := by sorry

alias «GlobalTheory».«TopExt».«mul_ιMulti_congr» := P2M_GlobalTheory_TopExt_mul__Multi_congr_3a4c7c8aee3c

-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TopExt_wedgeMul__Multi_72127a1483b7
-- name    : P2M_GlobalTheory_TopExt_wedgeMul__Multi_72127a1483b7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:43.310569+00:00
-- url     : https://prove2.me/theorems/f7542ead-04c8-51c5-b9e4-e62893fd5da8
-- title:
--   P2 M Global Theory Top Ext wedge Mul  Multi 72127a1483b7: P2 M Global Theory Top Ext wedge Mul  Multi 72127a1483b7
-- statement:
--   The P2 M Global Theory Top Ext wedge Mul  Multi 72127a1483b7 construction uses the P2 M Global Theory Top Ext wedge Mul  Multi 72127a1483b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L29-L32

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

theorem P2M_GlobalTheory_TopExt_wedgeMul__Multi_72127a1483b7 {a b : ℕ} (x : Fin a → H) (y : Fin b → H) :
    wedgeMul R H a b (exteriorPower.ιMulti R a x ⊗ₜ exteriorPower.ιMulti R b y) =
      exteriorPower.ιMulti R (a + b) (Fin.append x y) := by sorry

alias «GlobalTheory».«TopExt».«wedgeMul_ιMulti» := P2M_GlobalTheory_TopExt_wedgeMul__Multi_72127a1483b7

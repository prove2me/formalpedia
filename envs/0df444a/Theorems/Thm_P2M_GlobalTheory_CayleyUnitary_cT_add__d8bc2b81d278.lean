-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278
-- name    : P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:37:09.355854+00:00
-- url     : https://prove2.me/theorems/8d7ea7f4-4941-403d-9029-6499be769468
-- title:
--   P2 M Global Theory Cayley Unitary c T add  d8bc2b81d278: P2 M Global Theory Cayley Unitary c T add  d8bc2b81d278
-- statement:
--   The P2 M Global Theory Cayley Unitary c T add  d8bc2b81d278 construction uses the P2 M Global Theory Cayley Unitary c T add  d8bc2b81d278 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L11-L13

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CayleyUnitary
open Formalism.UG

theorem P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278 {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A + B) = cT σ A + cT σ B := by sorry

alias «GlobalTheory».«CayleyUnitary».«cT_add'» := P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278

-- Prove2me | Theorems.Thm_QEC_Locality_flipWordEquiv_apply
-- name    : QEC.Locality.flipWordEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:18.762033+00:00
-- url     : https://prove2.me/theorems/e69d4e63-8b62-4090-9bda-8bfce8a02e7c
-- title:
--   Locality: flip Word Equiv apply
-- statement:
--   The Locality construction uses the flip Word Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L654-L660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L654-L660

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.flipWordEquiv_apply {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) (x : Coding.Word (ZMod 2) α) :
    flipWordEquiv bits x =
      Qubit.flipSupport (PauliSymplectic.binarySupport x) bits := by sorry

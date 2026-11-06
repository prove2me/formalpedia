-- Prove2me | Theorems.Thm_QEC_Locality_inner_ket_eq_ite
-- name    : QEC.Locality.inner_ket_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:20.754616+00:00
-- url     : https://prove2.me/theorems/469aeb77-6286-4293-923c-b880c0d548bc
-- title:
--   Locality: inner ket eq ite
-- statement:
--   The Locality construction uses the inner ket eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L751-L754
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L751-L754

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

theorem QEC.Locality.inner_ket_eq_ite {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    inner Complex (ket a) (ket b) = if a = b then 1 else 0 := by sorry

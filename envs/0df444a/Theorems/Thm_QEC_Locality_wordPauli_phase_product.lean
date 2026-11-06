-- Prove2me | Theorems.Thm_QEC_Locality_wordPauli_phase_product
-- name    : QEC.Locality.wordPauli_phase_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:55.164205+00:00
-- url     : https://prove2.me/theorems/a5bc26e6-81c4-453b-b283-f43c33c73a46
-- title:
--   Locality: word Pauli phase product
-- statement:
--   The Locality construction uses the word Pauli phase product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L541-L568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L541-L568

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

theorem QEC.Locality.wordPauli_phase_product {α : Type u} [Fintype α] [DecidableEq α]
    (x z : Coding.Word (ZMod 2) α) (a b : Qubit.Bitstring α) :
    star (Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
      (Qubit.flipSupport (PauliSymplectic.binarySupport x) b)) *
      Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
        (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) =
      PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := α) z
          ((PauliSymplectic.bitstringWordEquiv α b) +
            PauliSymplectic.bitstringWordEquiv α a)) := by sorry

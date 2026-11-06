-- Prove2me | Theorems.Thm_QEC_Locality_wordBinaryPauli_apply_ket
-- name    : QEC.Locality.wordBinaryPauli_apply_ket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:04.88556+00:00
-- url     : https://prove2.me/theorems/f84a50ae-1724-470c-bb67-411666e697c2
-- title:
--   Locality: word Binary Pauli apply ket
-- statement:
--   The Locality construction uses the word Binary Pauli apply ket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L454-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L454-L479

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

theorem QEC.Locality.wordBinaryPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring S.SelectedCoordinates) :
    PauliSymplectic.toQubitOperator (wordBinaryPauli S p) (ket bits) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) bits •
        ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits) := by sorry

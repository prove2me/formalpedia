-- Prove2me | Theorems.Thm_QEC_Locality_wordPauli_contribution_matrix_element
-- name    : QEC.Locality.wordPauli_contribution_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:05.98173+00:00
-- url     : https://prove2.me/theorems/c8e41279-5ba5-4a57-83c4-35f09c5b7e36
-- title:
--   Locality: word Pauli contribution matrix element
-- statement:
--   The Locality construction uses the word Pauli contribution matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L570-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L570-L613

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

theorem QEC.Locality.wordPauli_contribution_matrix_element (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((wordPauliOperatorFactorized S p).comp
        (A.comp (LinearMap.adjoint (wordPauliOperatorFactorized S p))))
        (ket a ⊗ₜ[Complex] k)) =
      (PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) p.2
          ((PauliSymplectic.bitstringWordEquiv _ b) +
            PauliSymplectic.bitstringWordEquiv _ a))) *
        inner Complex
          (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
          (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) := by sorry

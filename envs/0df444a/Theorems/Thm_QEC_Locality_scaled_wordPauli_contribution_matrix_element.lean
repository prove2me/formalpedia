-- Prove2me | Theorems.Thm_QEC_Locality_scaled_wordPauli_contribution_matrix_element
-- name    : QEC.Locality.scaled_wordPauli_contribution_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:33.863364+00:00
-- url     : https://prove2.me/theorems/7953ccf3-325d-44f5-ad68-8dafc5a557b0
-- title:
--   Locality: scaled word Pauli contribution matrix element
-- statement:
--   The Locality construction uses the scaled word Pauli contribution matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L615-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L615-L646

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

theorem QEC.Locality.scaled_wordPauli_contribution_matrix_element (S : FiniteSubsystem ι)
    (c : Complex) (p : LocalPauliWordIndex S) (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((c • wordPauliOperatorFactorized S p).comp
        (A.comp (LinearMap.adjoint (c • wordPauliOperatorFactorized S p))))
        (ket a ⊗ₜ[Complex] k)) =
      (star c * c) *
        (PauliSymplectic.binaryPhaseScalar
          (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) p.2
            ((PauliSymplectic.bitstringWordEquiv _ b) +
              PauliSymplectic.bitstringWordEquiv _ a))) *
          inner Complex
            (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
            (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) := by sorry

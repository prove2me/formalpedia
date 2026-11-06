-- Prove2me | Theorems.Thm_QEC_Locality_wordPauliOperatorFactorized_adjoint_apply_tmul
-- name    : QEC.Locality.wordPauliOperatorFactorized_adjoint_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:46.942435+00:00
-- url     : https://prove2.me/theorems/8070cfae-ea04-4704-b41a-fa4cbea22c91
-- title:
--   Locality: word Pauli Operator Factorized adjoint apply tmul
-- statement:
--   The Locality construction uses the word Pauli Operator Factorized adjoint apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L491-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L491-L515

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

theorem QEC.Locality.wordPauliOperatorFactorized_adjoint_apply_tmul (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (a : Qubit.Bitstring S.SelectedCoordinates)
    (k : S.complementSystem) :
    (LinearMap.adjoint (wordPauliOperatorFactorized S p)) (ket a ⊗ₜ[Complex] k) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
        (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) •
      (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k) := by sorry

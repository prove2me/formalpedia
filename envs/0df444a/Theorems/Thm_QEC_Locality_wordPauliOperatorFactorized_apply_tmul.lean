-- Prove2me | Theorems.Thm_QEC_Locality_wordPauliOperatorFactorized_apply_tmul
-- name    : QEC.Locality.wordPauliOperatorFactorized_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:31.643196+00:00
-- url     : https://prove2.me/theorems/8b4a3e69-fb04-4340-b7dc-8001e52c443a
-- title:
--   Locality: word Pauli Operator Factorized apply tmul
-- statement:
--   The Locality construction uses the word Pauli Operator Factorized apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L481-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L481-L489

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

theorem QEC.Locality.wordPauliOperatorFactorized_apply_tmul (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (a : Qubit.Bitstring S.SelectedCoordinates)
    (k : S.complementSystem) :
    wordPauliOperatorFactorized S p (ket a ⊗ₜ[Complex] k) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) a •
        (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k) := by sorry

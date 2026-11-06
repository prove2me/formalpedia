-- Prove2me | Theorems.Thm_QEC_Locality_wordPauliTwirlFactorized_matrix_element
-- name    : QEC.Locality.wordPauliTwirlFactorized_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:11.532338+00:00
-- url     : https://prove2.me/theorems/702ff515-a994-4109-8233-73a16a7fab22
-- title:
--   Locality: word Pauli Twirl Factorized matrix element
-- statement:
--   The Locality construction uses the word Pauli Twirl Factorized matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L662-L749
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L662-L749

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

theorem QEC.Locality.wordPauliTwirlFactorized_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (wordPauliTwirlFactorized S A (ket a ⊗ₜ[Complex] k)) =
      if b = a then
        localPauliAmplitude S *
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k))
      else 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Locality_refill_comp_erasure_matrix_element
-- name    : QEC.Locality.refill_comp_erasure_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:47.367509+00:00
-- url     : https://prove2.me/theorems/59c55f16-48cc-4957-a7a4-4aa339fa4270
-- title:
--   Locality: refill comp erasure matrix element
-- statement:
--   The Locality construction uses the refill comp erasure matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L834-L920
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L834-L920

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

theorem QEC.Locality.refill_comp_erasure_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      ((QuantumChannel.comp (refillFactorized S) S.erasureChannel).toLinearMap A
        (ket a ⊗ₜ[Complex] k)) =
      if b = a then
        localPauliAmplitude S *
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k))
      else 0 := by sorry

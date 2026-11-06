-- Prove2me | Theorems.Thm_QEC_Locality_refill_contribution_matrix_element
-- name    : QEC.Locality.refill_contribution_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:33.731491+00:00
-- url     : https://prove2.me/theorems/279607bc-23a6-4713-9161-4603ad0542af
-- title:
--   Locality: refill contribution matrix element
-- statement:
--   The Locality construction uses the refill contribution matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L763-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L763-L785

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

theorem QEC.Locality.refill_contribution_matrix_element (S : FiniteSubsystem ι)
    (r : Qubit.Bitstring S.SelectedCoordinates)
    (B : Operator S.complementSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      ((tensorLeft S.selectedSystem S.complementSystem (ket r)).comp
        (B.comp (LinearMap.adjoint
          (tensorLeft S.selectedSystem S.complementSystem (ket r))))
        (ket a ⊗ₜ[Complex] k)) =
      inner Complex (ket b) (ket r) * inner Complex (ket r) (ket a) *
        inner Complex l (B k) := by sorry

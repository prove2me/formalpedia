-- Prove2me | Theorems.Thm_QEC_Locality_operator_ext_factorized_basis
-- name    : QEC.Locality.operator_ext_factorized_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:35.629576+00:00
-- url     : https://prove2.me/theorems/c41125c0-6c5f-435e-8a54-88a2e21ff171
-- title:
--   Locality: operator ext factorized basis
-- statement:
--   The Locality construction uses the operator ext factorized basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L356-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L356-L374

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

theorem QEC.Locality.operator_ext_factorized_basis (S : FiniteSubsystem ι)
    {A B : Operator S.factorizedSystem}
    (h : ∀ p q : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates,
      inner Complex (factorizedBasis S q) (A (factorizedBasis S p)) =
        inner Complex (factorizedBasis S q) (B (factorizedBasis S p))) :
    A = B := by sorry

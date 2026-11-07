-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
-- name    : QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:12:07.496204+00:00
-- url     : https://prove2.me/theorems/fee405bf-1baa-48d8-b28c-b2462a754158
-- title:
--   Pauli Symplectic: to Hermitian Qubit Operator apply
-- statement:
--   The Pauli Symplectic construction uses the to Hermitian Qubit Operator apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L47-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L47-L52

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply (P : Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι)
    (bits : Semantics.Qubit.Bitstring ι) :
    toHermitianQubitOperator P ψ bits =
      hermitianPhaseScalar P * toQubitOperator P ψ bits := by sorry

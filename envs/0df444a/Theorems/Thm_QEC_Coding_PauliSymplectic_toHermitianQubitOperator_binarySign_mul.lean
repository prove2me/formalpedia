-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binarySign_mul
-- name    : QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binarySign_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:50.963269+00:00
-- url     : https://prove2.me/theorems/08c138c3-d21d-48df-aa8f-a92ddb42db18
-- title:
--   Pauli Symplectic: to Hermitian Qubit Operator binary Sign mul
-- statement:
--   The original binary global phase remains the exact global Hermitian sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L136-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L136-L144

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

theorem QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binarySign_mul
    (phase : ZMod 2) (P : Binary ι) :
    toHermitianQubitOperator (binaryMul (binarySign phase) P) =
      binaryPhaseScalar phase • toHermitianQubitOperator P := by sorry

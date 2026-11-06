-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_mul_binaryMul
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_mul_binaryMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:07.816057+00:00
-- url     : https://prove2.me/theorems/8f4c5237-613e-49ef-8570-49baa3dfca0b
-- title:
--   Pauli Symplectic: to Qubit Operator mul binary Mul
-- statement:
--   The Pauli Symplectic construction uses the to Qubit Operator mul binary Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L923-L925
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L923-L925

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.toQubitOperator_mul_binaryMul (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator (binaryMul P Q) := by sorry

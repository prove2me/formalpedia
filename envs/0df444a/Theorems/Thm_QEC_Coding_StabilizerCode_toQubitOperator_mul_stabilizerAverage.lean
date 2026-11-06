-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mul_stabilizerAverage
-- name    : QEC.Coding.StabilizerCode.toQubitOperator_mul_stabilizerAverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:12.359197+00:00
-- url     : https://prove2.me/theorems/e0c548ea-3cc6-40f7-888a-dd354b5390ed
-- title:
--   Stabilizer Code: to Qubit Operator mul stabilizer Average
-- statement:
--   Left multiplication by a generated stabilizer fixes the finite group sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L354-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L354-L362

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.toQubitOperator_mul_stabilizerAverage
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (S : Q.GeneratedGroupElement) :
    toQubitOperator S.1 * Q.stabilizerAverage = Q.stabilizerAverage := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mem_code_of_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.toQubitOperator_mem_code_of_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:31.699223+00:00
-- url     : https://prove2.me/theorems/030bd42e-1651-45b9-9cb7-c89a75863c62
-- title:
--   Stabilizer Code: to Qubit Operator mem code of in Binary Normalizer
-- statement:
--   A normalizer Pauli preserves the exact common-fixed code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L410-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L410-L426

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

theorem QEC.Coding.StabilizerCode.toQubitOperator_mem_code_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) {P : Binary ι}
    (hN : Q.1.InBinaryNormalizer P)
    {ψ : Semantics.Qubit.QubitRegister ι} (hψ : ψ ∈ Q.1.code.carrier) :
    toQubitOperator P ψ ∈ Q.1.code.carrier := by sorry

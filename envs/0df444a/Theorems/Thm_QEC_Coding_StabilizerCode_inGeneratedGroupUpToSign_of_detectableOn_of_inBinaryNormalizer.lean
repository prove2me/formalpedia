-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:20.867022+00:00
-- url     : https://prove2.me/theorems/a461fb78-1c75-46ea-86c7-7329ac50cc5c
-- title:
--   Stabilizer Code: in Generated Group Up To Sign of detectable On of in Binary Normalizer
-- statement:
--   A detectable normalizer Pauli of a source-valid binary stabilizer code belongs
--   to the generated stabilizer up to the stored binary sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L482-L519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L482-L519

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

theorem QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    Q.1.InGeneratedGroupUpToSign E := by sorry

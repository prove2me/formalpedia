-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_of_inGeneratedGroupUpToSign
-- name    : QEC.Coding.StabilizerCode.detectableOn_of_inGeneratedGroupUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:23.171767+00:00
-- url     : https://prove2.me/theorems/815b3fa9-0495-43c6-addf-67ae2adb348b
-- title:
--   Stabilizer Code: detectable On of in Generated Group Up To Sign
-- statement:
--   The generated-group-up-to-sign branch is semantically detectable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L592-L601
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L592-L601

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

theorem QEC.Coding.StabilizerCode.detectableOn_of_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : Q.1.InGeneratedGroupUpToSign E) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) := by sorry

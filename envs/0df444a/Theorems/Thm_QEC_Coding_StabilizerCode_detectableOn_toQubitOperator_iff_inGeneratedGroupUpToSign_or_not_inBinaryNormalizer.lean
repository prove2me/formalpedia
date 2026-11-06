-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:51.067103+00:00
-- url     : https://prove2.me/theorems/2f701ba4-0849-48f6-b95b-831f1eb04562
-- title:
--   Stabilizer Code: detectable On to Qubit Operator iff in Generated Group Up To Sign or not in Binary Normalizer
-- statement:
--   A source-valid binary stabilizer code detects exactly the errors that belong to
--   the generated stabilizer up to the stored sign or lie outside its normalizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L617-L629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L617-L629

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

theorem QEC.Coding.StabilizerCode.detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InGeneratedGroupUpToSign E ∨ ¬ Q.1.InBinaryNormalizer E := by sorry

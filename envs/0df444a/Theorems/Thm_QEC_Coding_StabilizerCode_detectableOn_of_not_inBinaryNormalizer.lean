-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_of_not_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.detectableOn_of_not_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:37.875947+00:00
-- url     : https://prove2.me/theorems/8331f22d-41e5-4b0f-afdb-5aca957d97c9
-- title:
--   Stabilizer Code: detectable On of not in Binary Normalizer
-- statement:
--   The outside-normalizer branch is semantically detectable with scalar zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L604-L611
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L604-L611

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

theorem QEC.Coding.StabilizerCode.detectableOn_of_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : ¬ Q.1.InBinaryNormalizer E) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) := by sorry

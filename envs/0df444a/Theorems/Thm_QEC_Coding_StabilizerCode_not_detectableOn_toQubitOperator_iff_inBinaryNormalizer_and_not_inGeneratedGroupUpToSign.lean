-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
-- name    : QEC.Coding.StabilizerCode.not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:11.265878+00:00
-- url     : https://prove2.me/theorems/66560185-aff6-437b-8cc0-637e29c8d3c1
-- title:
--   Stabilizer Code: not detectable On to Qubit Operator iff in Binary Normalizer and not in Generated Group Up To Sign
-- statement:
--   Negating the source-valid stabilizer detectability characterization identifies
--   semantic nondetectability with the binary normalizer logical sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L39-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L39-L44

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι) :
    ¬ Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InBinaryNormalizer E ∧ ¬ Q.1.InGeneratedGroupUpToSign E := by sorry

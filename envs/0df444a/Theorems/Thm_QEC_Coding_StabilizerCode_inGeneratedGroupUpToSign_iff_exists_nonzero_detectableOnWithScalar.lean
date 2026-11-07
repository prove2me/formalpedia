-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar
-- name    : QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:11:30.267886+00:00
-- url     : https://prove2.me/theorems/dcb70a33-875c-405b-9339-0635dc014528
-- title:
--   Stabilizer Code: in Generated Group Up To Sign iff exists nonzero detectable On With Scalar
-- statement:
--   Generated-stabilizer membership up to binary sign is exactly nonzero scalar
--   action on the source-valid code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L40-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L40-L71

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Q.1.InGeneratedGroupUpToSign E ↔
      ∃ c : Complex, c ≠ 0 ∧
        Semantics.DetectableOnWithScalar Q.1.code (toQubitOperator E) c := by sorry

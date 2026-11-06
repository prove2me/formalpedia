-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_scalar_action_on_code_of_inGeneratedGroupUpToSign
-- name    : QEC.Coding.StabilizerCode.scalar_action_on_code_of_inGeneratedGroupUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:26.714201+00:00
-- url     : https://prove2.me/theorems/a5f6273e-8cd5-4010-adbf-c46f844afc7c
-- title:
--   Stabilizer Code: scalar action on code of in Generated Group Up To Sign
-- statement:
--   An element of a source-valid generated group, up to one stored sign, acts by
--   that same sign scalar on every code vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L525-L541
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L525-L541

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

theorem QEC.Coding.StabilizerCode.scalar_action_on_code_of_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : Q.1.InGeneratedGroupUpToSign E) :
    ∃ p : ZMod 2, ∀ ψ, ψ ∈ Q.1.code.carrier →
      toQubitOperator E ψ = binaryPhaseScalar p • ψ := by sorry

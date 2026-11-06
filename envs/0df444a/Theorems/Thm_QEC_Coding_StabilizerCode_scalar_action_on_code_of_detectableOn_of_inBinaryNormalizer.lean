-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:46.993985+00:00
-- url     : https://prove2.me/theorems/e8a2c0f1-27e7-48be-8923-ca047c257ddf
-- title:
--   Stabilizer Code: scalar action on code of detectable On of in Binary Normalizer
-- statement:
--   For a code-preserving error, the matrix-element detectability scalar is the
--   actual pointwise scalar action on the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L444-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L444-L463

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

theorem QEC.Coding.StabilizerCode.scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    ∃ c : Complex, ∀ ψ, ψ ∈ Q.1.code.carrier →
      toQubitOperator E ψ = c • ψ := by sorry

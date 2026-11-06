-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_matrixElement_eq_zero_of_not_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.matrixElement_eq_zero_of_not_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:19.059557+00:00
-- url     : https://prove2.me/theorems/7d36acf8-7f99-42b0-a396-8f7abc29c2d1
-- title:
--   Stabilizer Code: matrix Element eq zero of not in Binary Normalizer
-- statement:
--   An error outside the generated-group normalizer has zero matrix elements
--   between arbitrary vectors in the source-valid code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L547-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L547-L589

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

theorem QEC.Coding.StabilizerCode.matrixElement_eq_zero_of_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : ¬ Q.1.InBinaryNormalizer E) :
    ∀ ψ, ψ ∈ Q.1.code.carrier →
      ∀ φ, φ ∈ Q.1.code.carrier →
        inner Complex ψ (toQubitOperator E φ) = 0 := by sorry

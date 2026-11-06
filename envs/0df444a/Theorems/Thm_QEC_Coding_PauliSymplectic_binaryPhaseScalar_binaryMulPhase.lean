-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPhaseScalar_binaryMulPhase
-- name    : QEC.Coding.PauliSymplectic.binaryPhaseScalar_binaryMulPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:50.145688+00:00
-- url     : https://prove2.me/theorems/e237dcbf-bd27-45fe-9c22-1d86455afb63
-- title:
--   Pauli Symplectic: binary Phase Scalar binary Mul Phase
-- statement:
--   The Pauli Symplectic construction uses the binary Phase Scalar binary Mul Phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L584-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L584-L589

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.binaryPhaseScalar_binaryMulPhase (P Q : Binary ι) :
    binaryPhaseScalar (binaryMulPhase P Q) =
      binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
        binarySwapPhase Q.vector.xPart P.vector.zPart := by sorry

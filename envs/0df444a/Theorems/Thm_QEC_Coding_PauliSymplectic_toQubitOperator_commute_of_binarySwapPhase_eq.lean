-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_binarySwapPhase_eq
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_binarySwapPhase_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:23.976499+00:00
-- url     : https://prove2.me/theorems/013ff5d9-e56b-48b7-afab-bcb2b7849c26
-- title:
--   Pauli Symplectic: to Qubit Operator commute of binary Swap Phase eq
-- statement:
--   The Pauli Symplectic construction uses the to Qubit Operator commute of binary Swap Phase eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1074-L1108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1074-L1108

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_binarySwapPhase_eq (P Q : Binary ι)
    (hphase :
      binarySwapPhase Q.vector.xPart P.vector.zPart =
        binarySwapPhase P.vector.xPart Q.vector.zPart) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by sorry

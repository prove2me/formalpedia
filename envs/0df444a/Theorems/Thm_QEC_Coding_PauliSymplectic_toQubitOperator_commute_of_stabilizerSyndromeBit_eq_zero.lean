-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_stabilizerSyndromeBit_eq_zero
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_stabilizerSyndromeBit_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:45.692014+00:00
-- url     : https://prove2.me/theorems/424be76f-899f-4956-b310-a122a56fe8fa
-- title:
--   Pauli Symplectic: to Qubit Operator commute of stabilizer Syndrome Bit eq zero
-- statement:
--   A zero syndrome bit gives concrete commutation of the represented operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1594-L1598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1594-L1598

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_stabilizerSyndromeBit_eq_zero
    (M E : Binary ι) (h : stabilizerSyndromeBit M E = 0) :
    toQubitOperator E * toQubitOperator M = toQubitOperator M * toQubitOperator E := by sorry

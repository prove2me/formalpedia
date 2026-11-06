-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:13.405437+00:00
-- url     : https://prove2.me/theorems/70eebb8d-ae24-4b4e-a731-8537fd94b853
-- title:
--   Pauli Symplectic: to Qubit Operator commute of commutes
-- statement:
--   Binary symplectic commutation implies concrete commutation of the interpreted
--   finite qubit-register Pauli operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1114-L1117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1114-L1117

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_commutes (P Q : Binary ι) (h : Commutes P Q) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by sorry

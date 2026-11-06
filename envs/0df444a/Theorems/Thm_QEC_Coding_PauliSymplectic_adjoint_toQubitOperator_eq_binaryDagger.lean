-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger
-- name    : QEC.Coding.PauliSymplectic.adjoint_toQubitOperator_eq_binaryDagger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:31.028679+00:00
-- url     : https://prove2.me/theorems/8077d72e-b3ec-4b35-8630-4b63f4d62b12
-- title:
--   Pauli Symplectic: adjoint to Qubit Operator eq binary Dagger
-- statement:
--   The named binary dagger representative matches the adjoint of the interpreted
--   qubit-register operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L931-L975
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L931-L975

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

theorem QEC.Coding.PauliSymplectic.adjoint_toQubitOperator_eq_binaryDagger (P : Binary ι) :
    LinearMap.adjoint (toQubitOperator P) = toQubitOperator (binaryDagger P) := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_adjoint_comp_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:18:58.627221+00:00
-- url     : https://prove2.me/theorems/7528228b-c727-4c8d-95ba-d5b4608b62bc
-- title:
--   Pauli Symplectic: to Qubit Operator adjoint comp self
-- statement:
--   Interpreted binary Paulis are normalized at the finite-operator level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L982-L987
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L982-L987

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_adjoint_comp_self (P : Binary ι) :
    (LinearMap.adjoint (toQubitOperator P)).comp (toQubitOperator P) = 1 := by sorry

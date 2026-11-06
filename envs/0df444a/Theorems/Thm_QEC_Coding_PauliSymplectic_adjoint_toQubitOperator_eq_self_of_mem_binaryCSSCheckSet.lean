-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet
-- name    : QEC.Coding.PauliSymplectic.adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:29.582984+00:00
-- url     : https://prove2.me/theorems/0bc81ed7-22f3-4fc2-9125-260923c14646
-- title:
--   Pauli Symplectic: adjoint to Qubit Operator eq self of mem binary CSSCheck Set
-- statement:
--   CSS checks are interpreted as self-adjoint qubit-register operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2136-L2143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2136-L2143

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

theorem QEC.Coding.PauliSymplectic.adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet
    (xCode zCode : LinearCode (ZMod 2) ι) {S : Binary ι}
    (hS : S ∈ binaryCSSCheckSet xCode zCode) :
    LinearMap.adjoint (toQubitOperator S) = toQubitOperator S := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_exists_binaryCSSSemanticQuantumCodeOfDualLe
-- name    : QEC.Coding.PauliSymplectic.exists_binaryCSSSemanticQuantumCodeOfDualLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:28:30.481348+00:00
-- url     : https://prove2.me/theorems/a32c1dbc-3a8e-4549-8d93-0dbc8e3eb3e2
-- title:
--   Pauli Symplectic: exists binary CSSSemantic Quantum Code Of Dual Le
-- statement:
--   Raw binary CSS data satisfying dual containment realizes a semantic quantum-code
--   carrier whose elements are exactly the common fixed vectors of the generated
--   binary CSS checks, and those checks commute as concrete qubit-register
--   operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2894-L2906
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2894-L2906

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

theorem QEC.Coding.PauliSymplectic.exists_binaryCSSSemanticQuantumCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔
        ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
        ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
          toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by sorry

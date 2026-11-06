-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_exists_binaryStabilizerCommonFixedQuantumCode_of_commutes
-- name    : QEC.Coding.PauliSymplectic.exists_binaryStabilizerCommonFixedQuantumCode_of_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:28:21.767328+00:00
-- url     : https://prove2.me/theorems/53c7a23e-6ca8-4fc9-b54d-9e8c107aa963
-- title:
--   Pauli Symplectic: exists binary Stabilizer Common Fixed Quantum Code of commutes
-- statement:
--   Commuting binary stabilizer data determines the semantic common-fixed
--   `QuantumCode` carrier and supplies the concrete operator commutation bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2085-L2095
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2085-L2095

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

theorem QEC.Coding.PauliSymplectic.exists_binaryStabilizerCommonFixedQuantumCode_of_commutes
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔ ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by sorry

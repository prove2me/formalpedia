-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute
-- name    : QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:42.079897+00:00
-- url     : https://prove2.me/theorems/0b07b162-ddb3-43a7-a670-86e670475e05
-- title:
--   Pauli Symplectic: binary CSSQuantum Code Of Dual Le pairwise to Qubit Operator commute
-- statement:
--   The scoped binary CSS semantic code inherits concrete operator commutation from
--   dual containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2879-L2886
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2879-L2886

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

theorem QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
      ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by sorry

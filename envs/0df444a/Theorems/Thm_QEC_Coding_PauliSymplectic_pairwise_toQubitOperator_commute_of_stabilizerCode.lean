-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_pairwise_toQubitOperator_commute_of_stabilizerCode
-- name    : QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_stabilizerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:12.618183+00:00
-- url     : https://prove2.me/theorems/d9faeefb-45a7-4a1e-8ebf-f2eec8fb9187
-- title:
--   Pauli Symplectic: pairwise to Qubit Operator commute of stabilizer Code
-- statement:
--   Binary stabilizer-code specialization: the algebraic isotropic stabilizer field
--   is used only as input to the operator-level family bridge above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2101-L2106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2101-L2106

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

theorem QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_stabilizerCode
    (S : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    ∀ P : Binary ι, P ∈ S.stabilizers → ∀ Q : Binary ι, Q ∈ S.stabilizers →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P := by sorry

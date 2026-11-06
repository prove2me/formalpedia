-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_pairwise_toQubitOperator_commute_of_commutes
-- name    : QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:40.91317+00:00
-- url     : https://prove2.me/theorems/1d6012c5-9baf-4e35-97a4-08dac92da2d8
-- title:
--   Pauli Symplectic: pairwise to Qubit Operator commute of commutes
-- statement:
--   Family-level bridge from pairwise binary symplectic commutation to pairwise
--   commutation of the interpreted finite qubit-register operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2023-L2030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2023-L2030

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

theorem QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_commutes
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P := by sorry

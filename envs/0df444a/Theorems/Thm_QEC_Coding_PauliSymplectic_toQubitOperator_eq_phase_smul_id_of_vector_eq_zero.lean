-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:28.325779+00:00
-- url     : https://prove2.me/theorems/ad5f82c8-3226-449d-8d36-7f3184a3a898
-- title:
--   Pauli Symplectic: to Qubit Operator eq phase smul id of vector eq zero
-- statement:
--   If a binary Pauli has no X/Z support, its semantic operator is only its global phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L775-L783
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L775-L783

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
    {P : Binary ι}
    (hx : P.vector.xPart = 0)
    (hz : P.vector.zPart = 0) :
    toQubitOperator P =
      binaryPhaseScalar P.phase •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by sorry

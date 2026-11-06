-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_mul_expand
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_mul_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:23.137464+00:00
-- url     : https://prove2.me/theorems/f897321c-6d27-43df-9abf-76b4103dcbea
-- title:
--   Pauli Symplectic: to Qubit Operator mul expand
-- statement:
--   Raw product expansion for interpreted binary Pauli-symplectic representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L844-L851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L844-L851

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_mul_expand (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q =
      (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localZSupport (zSupport P)) *
          (Semantics.Qubit.localXSupport (xSupport Q) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by sorry

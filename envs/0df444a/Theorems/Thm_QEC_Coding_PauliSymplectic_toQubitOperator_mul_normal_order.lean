-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_mul_normal_order
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_mul_normal_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:37.814542+00:00
-- url     : https://prove2.me/theorems/d5eb0bc4-362a-4e8e-b102-e9d4ebf22007
-- title:
--   Pauli Symplectic: to Qubit Operator mul normal order
-- statement:
--   Downstream-facing product/phase bridge for binary Pauli-symplectic
--   representatives. This is the operator-level fact consumed before proving a
--   commutation theorem: the only nontrivial product phase is the support-overlap
--   sign from moving `P`'s `Z` support past `Q`'s `X` support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L859-L901
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L859-L901

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

theorem QEC.Coding.PauliSymplectic.toQubitOperator_mul_normal_order (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q =
      (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localXSupport (xSupport Q)) *
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by sorry

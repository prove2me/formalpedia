-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_xzSupport_mul_xzSupport_normal_order
-- name    : QEC.Coding.PauliSymplectic.xzSupport_mul_xzSupport_normal_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:17.607081+00:00
-- url     : https://prove2.me/theorems/36a33ff9-865f-4104-9b58-9a623a4d0e6b
-- title:
--   Pauli Symplectic: xz Support mul xz Support normal order
-- statement:
--   Normal-order product relation for binary support-level Paulis:
--   `(X x1 * Z z1) * (X x2 * Z z2)` is `X x1 * X x2 * Z z1 * Z z2`
--   with exactly the phase obtained by moving `z1` past `x2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L801-L841
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L801-L841

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

theorem QEC.Coding.PauliSymplectic.xzSupport_mul_xzSupport_normal_order
    (x1 z1 x2 z2 : Word (ZMod 2) ι) :
    ((Semantics.Qubit.localXSupport (binarySupport x1) *
          Semantics.Qubit.localZSupport (binarySupport z1)) *
        (Semantics.Qubit.localXSupport (binarySupport x2) *
          Semantics.Qubit.localZSupport (binarySupport z2))) =
      binarySwapPhase x2 z1 •
        ((Semantics.Qubit.localXSupport (binarySupport x1) *
            Semantics.Qubit.localXSupport (binarySupport x2)) *
          (Semantics.Qubit.localZSupport (binarySupport z1) *
            Semantics.Qubit.localZSupport (binarySupport z2))) := by sorry

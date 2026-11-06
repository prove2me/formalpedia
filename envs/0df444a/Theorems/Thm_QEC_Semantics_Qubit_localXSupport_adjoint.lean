-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_adjoint
-- name    : QEC.Semantics.Qubit.localXSupport_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:19.658728+00:00
-- url     : https://prove2.me/theorems/368b5606-7c5f-42e5-ab9e-9c4f97606433
-- title:
--   Qubit: local XSupport adjoint
-- statement:
--   Support-level `X` operators are self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L82-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L82-L99

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
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators
universe u
variable {ι : Type u}
variable [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Qubit.localXSupport_adjoint (s : Finset ι) :
    LinearMap.adjoint (localXSupport s) = localXSupport s := by sorry

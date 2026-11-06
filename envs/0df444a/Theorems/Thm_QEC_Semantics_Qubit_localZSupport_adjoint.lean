-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_adjoint
-- name    : QEC.Semantics.Qubit.localZSupport_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:26.676665+00:00
-- url     : https://prove2.me/theorems/3f63bb73-40c8-4559-a7bf-9c88d6af1ae1
-- title:
--   Qubit: local ZSupport adjoint
-- statement:
--   Support-level `Z` operators are self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L102-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L102-L119

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

theorem QEC.Semantics.Qubit.localZSupport_adjoint (s : Finset ι) :
    LinearMap.adjoint (localZSupport s) = localZSupport s := by sorry

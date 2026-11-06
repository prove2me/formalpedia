-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_commute
-- name    : QEC.Semantics.Qubit.localXSupport_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:25.538496+00:00
-- url     : https://prove2.me/theorems/39080b00-8bb6-4f38-ad9c-7ca2a11eaf64
-- title:
--   Qubit: local XSupport commute
-- statement:
--   Support-level `X` operators commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L41-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L41-L44

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

theorem QEC.Semantics.Qubit.localXSupport_commute (s t : Finset ι) :
    localXSupport s * localXSupport t = localXSupport t * localXSupport s := by sorry

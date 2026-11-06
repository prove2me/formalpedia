-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_localXSupport_phase
-- name    : QEC.Semantics.Qubit.localZSupport_localXSupport_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:34.637536+00:00
-- url     : https://prove2.me/theorems/3a903619-5aed-4e0b-a2cd-3866063ecbca
-- title:
--   Qubit: local ZSupport local XSupport phase
-- statement:
--   Moving a support-level `Z` past a support-level `X` gives the same binary sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L73-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L73-L79

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

theorem QEC.Semantics.Qubit.localZSupport_localXSupport_phase (xSupport zSupport : Finset ι) :
    localZSupport zSupport * localXSupport xSupport =
      supportPhaseSign xSupport zSupport •
        (localXSupport xSupport * localZSupport zSupport) := by sorry

-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_supportPhaseSign_mul_self
-- name    : QEC.Semantics.Qubit.supportPhaseSign_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:22.747202+00:00
-- url     : https://prove2.me/theorems/861cf731-40ed-4bbc-a53e-a3cc5e70984f
-- title:
--   Qubit: support Phase Sign mul self
-- statement:
--   The support swap sign is its own inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L64-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L64-L70

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
omit [Fintype ι]

theorem QEC.Semantics.Qubit.supportPhaseSign_mul_self (xSupport zSupport : Finset ι) :
    supportPhaseSign xSupport zSupport * supportPhaseSign xSupport zSupport = 1 := by sorry

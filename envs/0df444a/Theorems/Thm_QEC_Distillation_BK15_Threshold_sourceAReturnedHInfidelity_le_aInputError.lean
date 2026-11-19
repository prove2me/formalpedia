-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_sourceAReturnedHInfidelity_le_aInputError
-- name    : QEC.Distillation.BK15.Threshold.sourceAReturnedHInfidelity_le_aInputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:25:41.693739+00:00
-- url     : https://prove2.me/theorems/c259ed77-d258-43d1-a0e9-eaddd2a1e788
-- title:
--   Threshold: source AReturned HInfidelity le a Input Error
-- statement:
--   Any source-A density, transported back by the inverse source frame, has
--   H-infidelity no greater than its negative-A error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1140-L1174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1140-L1174

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.sourceAReturnedHInfidelity_le_aInputError
    (sigma : DensityOperator QubitSpace) :
    1 - hFidelity (sourceA0Transport.symm.conjDensity sigma) ^ 2 <=
      aInputError sigma := by sorry

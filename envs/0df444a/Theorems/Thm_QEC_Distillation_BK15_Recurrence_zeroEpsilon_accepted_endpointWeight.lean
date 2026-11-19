-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_zeroEpsilon_accepted_endpointWeight
-- name    : QEC.Distillation.BK15.Recurrence.zeroEpsilon_accepted_endpointWeight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:16:29.190454+00:00
-- url     : https://prove2.me/theorems/938df86f-2a5e-4915-a92e-82fc3701196c
-- title:
--   Recurrence: zero Epsilon accepted endpoint Weight
-- statement:
--   The closed zero-noise input has accepted raw physical mass one.  This is
--   an endpoint statement, not a normalized rejected branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2536-L2539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2536-L2539

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct

theorem QEC.Distillation.BK15.Recurrence.zeroEpsilon_accepted_endpointWeight :
    endpointWeight zeroEpsilon .accepted = 1 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15RawZeroEndpoint_is_ideal
-- name    : QEC.Distillation.BK15.Threshold.bk15RawZeroEndpoint_is_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:31:10.208587+00:00
-- url     : https://prove2.me/theorems/a56519a1-cc76-407b-9e45-096df053adbe
-- title:
--   Threshold: bk15 Raw Zero Endpoint is ideal
-- statement:
--   The raw zero-error endpoint is ideal under the complete decoded operation;
--   this is deliberately separate from normalized accepted/rejected branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1198-L1200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1198-L1200

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15RawZeroEndpoint_is_ideal :
    decodedOperation.mapDensity (rawInput zeroEpsilon) = aZeroDensity := by sorry

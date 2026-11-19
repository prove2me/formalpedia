-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_zeroEpsilon_decoded_output_error
-- name    : QEC.Distillation.BK15.Recurrence.zeroEpsilon_decoded_output_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:31.376475+00:00
-- url     : https://prove2.me/theorems/5e5616cd-693c-46d1-8e7e-d1fd6de3f34f
-- title:
--   Recurrence: zero Epsilon decoded output error
-- statement:
--   The actual full decoded BK15 operation sends the closed zero-noise input
--   to the ideal A-frame density, so its physical output error is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2543-L2554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2543-L2554

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

theorem QEC.Distillation.BK15.Recurrence.zeroEpsilon_decoded_output_error :
    bk15OutputError (decodedOperation.mapDensity (rawInput zeroEpsilon))
      aZeroDensity = 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_cubic_limit
-- name    : QEC.Distillation.BK15.Threshold.bk15Recurrence_cubic_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:29:44.14061+00:00
-- url     : https://prove2.me/theorems/478e544d-cb70-46b4-a74b-be5c6c647f89
-- title:
--   Threshold: bk15 Recurrence cubic limit
-- statement:
--   The actual accepted-error recurrence has leading small-error coefficient
--   `35`, in the one-sided physical limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L726-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L726-L736

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

theorem QEC.Distillation.BK15.Threshold.bk15Recurrence_cubic_limit :
    Filter.Tendsto (fun epsilon : Real => bk15Recurrence epsilon / epsilon ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 35) := by sorry

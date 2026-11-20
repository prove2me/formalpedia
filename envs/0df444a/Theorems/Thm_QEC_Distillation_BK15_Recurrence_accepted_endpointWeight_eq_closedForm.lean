-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_endpointWeight_eq_closedForm
-- name    : QEC.Distillation.BK15.Recurrence.accepted_endpointWeight_eq_closedForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:00.450767+00:00
-- url     : https://prove2.me/theorems/92145730-d975-44e0-9417-395de003a241
-- title:
--   Recurrence: accepted endpoint Weight eq closed Form
-- statement:
--   The accepted physical Born mass has the BK15 closed form derived from the
--   literal dual-word enumerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2399-L2405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2399-L2405

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
set_option linter.constructorNameAsVariable false

theorem QEC.Distillation.BK15.Recurrence.accepted_endpointWeight_eq_closedForm (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted =
      (1 + 15 * bk15_r epsilon ^ 8) / 16 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_endpointWeight_eq_l1Dual_wordSum
-- name    : QEC.Distillation.BK15.Recurrence.accepted_endpointWeight_eq_l1Dual_wordSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:16:28.190573+00:00
-- url     : https://prove2.me/theorems/1cb6b6ad-b1a7-4ad1-942d-341d8dfb8449
-- title:
--   Recurrence: accepted endpoint Weight eq l1 Dual word Sum
-- statement:
--   The concrete accepted endpoint is exactly the independent word-weight
--   sum over the enumerated dual of the four linear checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

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

theorem QEC.Distillation.BK15.Recurrence.accepted_endpointWeight_eq_l1Dual_wordSum (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted =
      ∑ word ∈ l1DualWords, bk15WordWeight epsilon word := by sorry

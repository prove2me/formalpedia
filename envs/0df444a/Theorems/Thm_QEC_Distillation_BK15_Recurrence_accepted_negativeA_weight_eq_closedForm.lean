-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_negativeA_weight_eq_closedForm
-- name    : QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_closedForm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:16:40.132608+00:00
-- url     : https://prove2.me/theorems/621abbab-68da-4782-9dca-208898820e1c
-- title:
--   Recurrence: accepted negative A weight eq closed Form
-- statement:
--   The decoded negative-A raw numerator has the BK15 logical-coset closed
--   form derived from its exact finite weight enumerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2410-L2417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2410-L2417

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

theorem QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_closedForm (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / 32 := by sorry

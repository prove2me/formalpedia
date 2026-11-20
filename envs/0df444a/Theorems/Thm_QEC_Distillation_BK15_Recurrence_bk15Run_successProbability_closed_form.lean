-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15Run_successProbability_closed_form
-- name    : QEC.Distillation.BK15.Recurrence.bk15Run_successProbability_closed_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:41.794959+00:00
-- url     : https://prove2.me/theorems/57ea23ef-0754-4585-bd68-ca39a9b7cd40
-- title:
--   Recurrence: bk15 Run success Probability closed form
-- statement:
--   The packaged BK15 run has the source acceptance probability, derived from
--   the literal accepted physical endpoint rather than stored as a formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2512-L2516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2512-L2516

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

theorem QEC.Distillation.BK15.Recurrence.bk15Run_successProbability_closed_form
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).successProbability =
      (1 + 15 * bk15_r epsilon ^ 8) / 16 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Bias_eq_recurrence_bias
-- name    : QEC.Distillation.BK15.Threshold.bk15Bias_eq_recurrence_bias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:28:59.96809+00:00
-- url     : https://prove2.me/theorems/976a0262-e0e0-471e-86c9-d87f94c8e4d4
-- title:
--   Threshold: bk15 Bias eq recurrence bias
-- statement:
--   The Threshold construction uses the bk15 Bias eq recurrence bias property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L41-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L41-L43

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

theorem QEC.Distillation.BK15.Threshold.bk15Bias_eq_recurrence_bias (epsilon : BK15Epsilon) :
    bk15Bias epsilon.epsilon = bk15_r epsilon := by sorry

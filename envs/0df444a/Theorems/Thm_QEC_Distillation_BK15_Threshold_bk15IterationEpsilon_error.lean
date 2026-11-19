-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15IterationEpsilon_error
-- name    : QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:24:44.016941+00:00
-- url     : https://prove2.me/theorems/b2f423ae-0d11-4546-8e37-b1c10e38b3e3
-- title:
--   Threshold: bk15 Iteration Epsilon error
-- statement:
--   The Threshold construction uses the bk15 Iteration Epsilon error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L635-L639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L635-L639

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

theorem QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    (bk15IterationEpsilon epsilon hpositive hthreshold rounds).epsilon =
      bk15Iteration epsilon rounds := by sorry

attribute [defeq] QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error

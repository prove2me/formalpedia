-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_fixed_iff
-- name    : QEC.Distillation.BK15.Threshold.bk15Recurrence_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:26:23.303543+00:00
-- url     : https://prove2.me/theorems/8133ebef-ffe8-4968-8c4d-cb526b6106b7
-- title:
--   Threshold: bk15 Recurrence fixed iff
-- statement:
--   The Threshold construction uses the bk15 Recurrence fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L364-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L364-L393

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

theorem QEC.Distillation.BK15.Threshold.bk15Recurrence_fixed_iff
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk15Recurrence epsilon = epsilon ↔
      epsilon = 0 ∨ epsilon = epsilonStar ∨ epsilon = 1 / 2 := by sorry

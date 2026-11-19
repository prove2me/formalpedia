-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_epsilonStar_rational_bracket
-- name    : QEC.Distillation.BK15.Threshold.epsilonStar_rational_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:26:51.156789+00:00
-- url     : https://prove2.me/theorems/59897ccf-9858-46d3-9998-88c0b7aadc5e
-- title:
--   Threshold: epsilon Star rational bracket
-- statement:
--   The Threshold construction uses the epsilon Star rational bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L324-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L324-L337

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

theorem QEC.Distillation.BK15.Threshold.epsilonStar_rational_bracket :
    14147 / 100000 < epsilonStar ∧ epsilonStar < 14149 / 100000 := by sorry

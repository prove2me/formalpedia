-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_FStar_nonneg
-- name    : QEC.Distillation.BK15.Threshold.FStar_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:25:26.140314+00:00
-- url     : https://prove2.me/theorems/14b37f04-a0ae-44f6-aaa4-a6773568f4bb
-- title:
--   Threshold: FStar nonneg
-- statement:
--   The Threshold construction uses the FStar nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L756-L757
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L756-L757

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

theorem QEC.Distillation.BK15.Threshold.FStar_nonneg : 0 <= FStar := by sorry

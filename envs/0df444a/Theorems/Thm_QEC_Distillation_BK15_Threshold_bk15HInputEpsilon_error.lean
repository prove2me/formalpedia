-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInputEpsilon_error
-- name    : QEC.Distillation.BK15.Threshold.bk15HInputEpsilon_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:30:05.573201+00:00
-- url     : https://prove2.me/theorems/8284c7bc-ec22-43eb-964a-23e968a23913
-- title:
--   Threshold: bk15 HInput Epsilon error
-- statement:
--   The Threshold construction uses the bk15 HInput Epsilon error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L817-L822
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L817-L822

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

theorem QEC.Distillation.BK15.Threshold.bk15HInputEpsilon_error
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    (bk15HInputEpsilon rho hpositive hleHalf).epsilon = bk15HInputError rho := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInputError_lt_epsilonStar_of_FStar_lt
-- name    : QEC.Distillation.BK15.Threshold.bk15HInputError_lt_epsilonStar_of_FStar_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:27:17.322752+00:00
-- url     : https://prove2.me/theorems/9f52a77b-908c-4140-a001-7d5f19ac0a51
-- title:
--   Threshold: bk15 HInput Error lt epsilon Star of FStar lt
-- statement:
--   The strict H-fidelity criterion is precisely strong enough for the
--   certified source-A recurrence threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L784-L792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L784-L792

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

theorem QEC.Distillation.BK15.Threshold.bk15HInputError_lt_epsilonStar_of_FStar_lt
    (rho : DensityOperator QubitSpace) (hfidelity : FStar < hFidelity rho) :
    bk15HInputError rho < epsilonStar := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_r_nonneg
-- name    : QEC.Distillation.BK15.Recurrence.bk15_r_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:30.653257+00:00
-- url     : https://prove2.me/theorems/39cda1df-d4b7-4e82-a172-12832803cc2d
-- title:
--   Recurrence: bk15 r nonneg
-- statement:
--   The physical source interval puts the signed bias in the nonnegative half
--   of the unit interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L29-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L29-L31

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

theorem QEC.Distillation.BK15.Recurrence.bk15_r_nonneg (epsilon : BK15Epsilon) : 0 ≤ bk15_r epsilon := by sorry

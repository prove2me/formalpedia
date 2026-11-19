-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_r_le_one
-- name    : QEC.Distillation.BK15.Recurrence.bk15_r_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:36.581771+00:00
-- url     : https://prove2.me/theorems/1860641e-da4f-4c67-a272-2bbc43b86986
-- title:
--   Recurrence: bk15 r le one
-- statement:
--   The same physical interval bounds the signed bias above by one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L34-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L34-L36

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

theorem QEC.Distillation.BK15.Recurrence.bk15_r_le_one (epsilon : BK15Epsilon) : bk15_r epsilon ≤ 1 := by sorry

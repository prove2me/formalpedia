-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l2DualWords_iff
-- name    : QEC.Distillation.BK15.mem_l2DualWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:05:47.062315+00:00
-- url     : https://prove2.me/theorems/1d5d4001-428e-4b7e-b294-6dbdf94a7fe6
-- title:
--   BK15: mem l2 Dual Words iff
-- statement:
--   The finite enumeration `l2DualWords` is extensionally the dual of `L2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L581-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L581-L592

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.mem_l2DualWords_iff (w : Word) : w ∈ l2DualWords ↔ w ∈ L2.dual.carrier := by sorry

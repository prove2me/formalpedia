-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l1DualWords_iff
-- name    : QEC.Distillation.BK15.mem_l1DualWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:05:36.195368+00:00
-- url     : https://prove2.me/theorems/bf31e95e-0331-487b-b9d8-2d9614f30964
-- title:
--   BK15: mem l1 Dual Words iff
-- statement:
--   The finite enumeration `l1DualWords` is extensionally the dual of `L1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L567-L578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L567-L578

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
set_option maxRecDepth 16384

theorem QEC.Distillation.BK15.mem_l1DualWords_iff (w : Word) : w ∈ l1DualWords ↔ w ∈ L1.dual.carrier := by sorry

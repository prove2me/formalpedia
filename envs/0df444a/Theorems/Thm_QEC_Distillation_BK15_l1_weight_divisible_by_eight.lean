-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_weight_divisible_by_eight
-- name    : QEC.Distillation.BK15.l1_weight_divisible_by_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:00.031322+00:00
-- url     : https://prove2.me/theorems/3003840e-73bb-4855-ab7c-816a08943b14
-- title:
--   BK15: l1 weight divisible by eight
-- statement:
--   All `L1` weights are divisible by eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L484-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L484-L486

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_weight_divisible_by_eight :
    ∀ a : Fin 4 → Bit, HammingWeight (l1CoefficientMap a) % 8 = 0 := by sorry

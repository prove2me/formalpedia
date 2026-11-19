-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2Dual_weight_enumerator
-- name    : QEC.Distillation.BK15.l2Dual_weight_enumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:06:33.430656+00:00
-- url     : https://prove2.me/theorems/577fd680-964f-4b5d-b3db-85f2fd5fc426
-- title:
--   BK15: l2 Dual weight enumerator
-- statement:
--   Exact finite weight enumerator of the proved dual `L2⊥`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L678-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L678-L685

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2Dual_weight_enumerator (weight : Fin 16) :
    weightCount l2DualWords weight.1 =
      if weight = 0 then 1 else if weight = 7 then 15 else
      if weight = 8 then 15 else if weight = 15 then 1 else 0 := by sorry

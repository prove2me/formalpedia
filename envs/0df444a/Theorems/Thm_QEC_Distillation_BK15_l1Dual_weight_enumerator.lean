-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1Dual_weight_enumerator
-- name    : QEC.Distillation.BK15.l1Dual_weight_enumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:06:19.438201+00:00
-- url     : https://prove2.me/theorems/e45dc0ff-4f4f-428f-83dd-bcea1b626863
-- title:
--   BK15: l1 Dual weight enumerator
-- statement:
--   Exact finite weight enumerator of the proved dual `L1⊥`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L663-L675
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L663-L675

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1Dual_weight_enumerator (weight : Fin 16) :
    weightCount l1DualWords weight.1 =
      if weight = 0 then 1 else if weight = 3 then 35 else
      if weight = 4 then 105 else if weight = 5 then 168 else
      if weight = 6 then 280 else if weight = 7 then 435 else
      if weight = 8 then 435 else if weight = 9 then 280 else
      if weight = 10 then 168 else if weight = 11 then 105 else
      if weight = 12 then 35 else if weight = 15 then 1 else 0 := by sorry

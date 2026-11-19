-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_weight_enumerator
-- name    : QEC.Distillation.BK15.l2_weight_enumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:06:19.720812+00:00
-- url     : https://prove2.me/theorems/d477ee22-93e5-4a79-9afb-50f8c5470659
-- title:
--   BK15: l2 weight enumerator
-- statement:
--   Exact finite weight enumerator of `L2`, computed from its explicit image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L638-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L638-L646

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_weight_enumerator (weight : Fin 16) :
    weightCount l2Words weight.1 =
      if weight = 0 then 1 else if weight = 4 then 105 else
      if weight = 6 then 280 else if weight = 8 then 435 else
      if weight = 10 then 168 else if weight = 12 then 35 else 0 := by sorry

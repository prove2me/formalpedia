-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_weight_enumerator
-- name    : QEC.Distillation.BK15.l1_weight_enumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:06:00.494135+00:00
-- url     : https://prove2.me/theorems/5bb25e2b-6000-4dc1-a5f3-901c1b241303
-- title:
--   BK15: l1 weight enumerator
-- statement:
--   Exact finite weight enumerator of `L1`, computed from its explicit image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L629-L635
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L629-L635

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_weight_enumerator (weight : Fin 16) :
    weightCount l1Words weight.1 =
      if weight = 0 then 1 else if weight = 8 then 15 else 0 := by sorry

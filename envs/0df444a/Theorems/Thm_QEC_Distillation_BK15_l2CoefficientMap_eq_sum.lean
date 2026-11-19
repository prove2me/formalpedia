-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_eq_sum
-- name    : QEC.Distillation.BK15.l2CoefficientMap_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:55:05.266432+00:00
-- url     : https://prove2.me/theorems/255371fb-9786-4702-9602-e10dd5a79a2c
-- title:
--   BK15: l2 Coefficient Map eq sum
-- statement:
--   Expand an `L2` word in its ten concrete generator words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L416-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L416-L419

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2CoefficientMap_eq_sum (b : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap b = ∑ g : Sum (Fin 4) QuadraticIndex, b g • l2Generator g := by sorry

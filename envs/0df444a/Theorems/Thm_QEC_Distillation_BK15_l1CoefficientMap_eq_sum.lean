-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
-- name    : QEC.Distillation.BK15.l1CoefficientMap_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:55:00.910508+00:00
-- url     : https://prove2.me/theorems/fcfb3dfd-8bd8-466b-b352-f756e7600782
-- title:
--   BK15: l1 Coefficient Map eq sum
-- statement:
--   Expand an `L1` word in its four concrete generator words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L410-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L410-L413

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1CoefficientMap_eq_sum (a : Fin 4 → Bit) :
    l1CoefficientMap a = ∑ j : Fin 4, a j • linearGenerator j := by sorry

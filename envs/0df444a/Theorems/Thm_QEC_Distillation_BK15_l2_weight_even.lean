-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_weight_even
-- name    : QEC.Distillation.BK15.l2_weight_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:17.799501+00:00
-- url     : https://prove2.me/theorems/442ca7fc-24a1-420b-8baa-7304ff5d3553
-- title:
--   BK15: l2 weight even
-- statement:
--   All `L2` weights are even.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L489-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L489-L492

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_weight_even :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit,
      HammingWeight (l2CoefficientMap b) % 2 = 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_pointwiseProduct_weight_divisible_by_four
-- name    : QEC.Distillation.BK15.l1_pointwiseProduct_weight_divisible_by_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:17.164206+00:00
-- url     : https://prove2.me/theorems/3732197d-49d0-4e18-b6dd-8e1dcfd26586
-- title:
--   BK15: l1 pointwise Product weight divisible by four
-- statement:
--   Products of two `L1` words have weight divisible by four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L495-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L495-L498

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_pointwiseProduct_weight_divisible_by_four :
    ∀ (a b : Fin 4 → Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l1CoefficientMap b)) % 4 = 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_l2Dual_pointwiseProduct_weight_divisible_by_four
-- name    : QEC.Distillation.BK15.l1_l2Dual_pointwiseProduct_weight_divisible_by_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:15.930479+00:00
-- url     : https://prove2.me/theorems/76a53710-ac70-4ead-9d7a-8b022473ae6f
-- title:
--   BK15: l1 l2 Dual pointwise Product weight divisible by four
-- statement:
--   Products of an `L1` word with an `L2`-dual word have weight divisible by four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L501-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L501-L504

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_l2Dual_pointwiseProduct_weight_divisible_by_four :
    ∀ (a : Fin 4 → Bit) (ac : (Fin 4 → Bit) × Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l2DualCoefficientMap ac)) % 4 = 0 := by sorry

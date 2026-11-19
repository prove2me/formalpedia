-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_coefficient_has_l2_presentation
-- name    : QEC.Distillation.BK15.l1_coefficient_has_l2_presentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:53:05.159903+00:00
-- url     : https://prove2.me/theorems/a7a35921-0efa-4474-80d4-060a00bb1265
-- title:
--   BK15: l1 coefficient has l2 presentation
-- statement:
--   `L1` is concretely contained in the degree-at-most-two code `L2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L255-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L255-L259

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_coefficient_has_l2_presentation :
    ∀ a : Fin 4 → Bit,
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit,
        l2CoefficientMap b = l1CoefficientMap a := by sorry

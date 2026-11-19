-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_linearGenerator_is_l1_coefficient_image
-- name    : QEC.Distillation.BK15.linearGenerator_is_l1_coefficient_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:54:58.494695+00:00
-- url     : https://prove2.me/theorems/f70bf363-5b4e-4971-aedd-e2585541dd40
-- title:
--   BK15: linear Generator is l1 coefficient image
-- statement:
--   Each displayed linear generator is a coefficient-map image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L392-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L392-L394

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.linearGenerator_is_l1_coefficient_image :
    ∀ j : Fin 4, l1CoefficientMap (Pi.single j 1) = linearGenerator j := by sorry

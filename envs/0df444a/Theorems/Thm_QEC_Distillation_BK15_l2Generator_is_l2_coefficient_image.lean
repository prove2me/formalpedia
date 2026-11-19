-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2Generator_is_l2_coefficient_image
-- name    : QEC.Distillation.BK15.l2Generator_is_l2_coefficient_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:54:52.871655+00:00
-- url     : https://prove2.me/theorems/b23d1b3f-355f-426e-b884-c49576bb080a
-- title:
--   BK15: l2 Generator is l2 coefficient image
-- statement:
--   Each displayed degree-at-most-two generator is a coefficient-map image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L397-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L397-L400

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2Generator_is_l2_coefficient_image :
    ∀ g : Sum (Fin 4) QuadraticIndex,
      l2CoefficientMap (Pi.single g 1) = l2Generator g := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2DualCoefficientMap_injective
-- name    : QEC.Distillation.BK15.l2DualCoefficientMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:32.498104+00:00
-- url     : https://prove2.me/theorems/38f8bff3-2c16-4aef-b877-c26ae37ccc7a
-- title:
--   BK15: l2 Dual Coefficient Map injective
-- statement:
--   The two direct-sum coefficient presentations are injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L218-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L218-L220

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2DualCoefficientMap_injective : Function.Injective l2DualCoefficientMap := by sorry

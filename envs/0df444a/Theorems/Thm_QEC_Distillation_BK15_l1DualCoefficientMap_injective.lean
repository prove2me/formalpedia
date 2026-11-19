-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1DualCoefficientMap_injective
-- name    : QEC.Distillation.BK15.l1DualCoefficientMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:21.825119+00:00
-- url     : https://prove2.me/theorems/91ec8741-0122-4feb-b9a6-83d3fe632ba2
-- title:
--   BK15: l1 Dual Coefficient Map injective
-- statement:
--   The two direct-sum coefficient presentations are injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L212-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L212-L215

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1DualCoefficientMap_injective : Function.Injective l1DualCoefficientMap := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_injective
-- name    : QEC.Distillation.BK15.l1CoefficientMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:31.373189+00:00
-- url     : https://prove2.me/theorems/552d5c66-8f21-4fcf-8dfe-25282256de03
-- title:
--   BK15: l1 Coefficient Map injective
-- statement:
--   The four selected linear evaluations have no coefficient redundancy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L202-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L202-L204

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1CoefficientMap_injective : Function.Injective l1CoefficientMap := by sorry

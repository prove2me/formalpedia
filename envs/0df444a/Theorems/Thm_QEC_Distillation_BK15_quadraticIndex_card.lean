-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_quadraticIndex_card
-- name    : QEC.Distillation.BK15.quadraticIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:41.693043+00:00
-- url     : https://prove2.me/theorems/2abbac91-3cd9-4586-9cbe-1c4ae8058cd8
-- title:
--   BK15: quadratic Index card
-- statement:
--   The six source monomials are the six ordered pairs in four variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L198-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L198-L199

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.quadraticIndex_card : Fintype.card QuadraticIndex = 6 := by sorry

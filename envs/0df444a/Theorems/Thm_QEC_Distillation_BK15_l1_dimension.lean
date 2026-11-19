-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_dimension
-- name    : QEC.Distillation.BK15.l1_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:50.132205+00:00
-- url     : https://prove2.me/theorems/b0158f52-c73c-4870-be63-ba4e0301c3b4
-- title:
--   BK15: l1 dimension
-- statement:
--   The BK05 `L1` code has its source dimension four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L223-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L223-L228

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_dimension : Dimension L1 = 4 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_L2_le_L1_dual
-- name    : QEC.Distillation.BK15.L2_le_L1_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:01:17.477726+00:00
-- url     : https://prove2.me/theorems/77df4d2f-b9d1-4516-9997-9c427eb703a7
-- title:
--   BK15: L2 le L1 dual
-- statement:
--   The concrete `L2` code lies in the dual of `L1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L273-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L273-L277

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.L2_le_L1_dual : L2.carrier ≤ L1.dual.carrier := by sorry

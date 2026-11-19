-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_l1Syndrome_ker
-- name    : QEC.Distillation.BK15.l1_dual_carrier_eq_l1Syndrome_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:03:46.816693+00:00
-- url     : https://prove2.me/theorems/c36c22a7-9fc4-4f65-8f76-d4ed70694689
-- title:
--   BK15: l1 dual carrier eq l1 Syndrome ker
-- statement:
--   The `L1` dual is exactly the kernel of its four concrete parity checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L454-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L454-L466

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_dual_carrier_eq_l1Syndrome_ker :
    L1.dual.carrier = LinearMap.ker l1Syndrome := by sorry

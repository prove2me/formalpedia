-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_l2Syndrome_ker
-- name    : QEC.Distillation.BK15.l2_dual_carrier_eq_l2Syndrome_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:03:51.275991+00:00
-- url     : https://prove2.me/theorems/dcd2fce6-4e0d-406c-b1ed-107124019f06
-- title:
--   BK15: l2 dual carrier eq l2 Syndrome ker
-- statement:
--   The `L2` dual is exactly the kernel of its ten concrete parity checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L469-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L469-L481

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_dual_carrier_eq_l2Syndrome_ker :
    L2.dual.carrier = LinearMap.ker l2Syndrome := by sorry

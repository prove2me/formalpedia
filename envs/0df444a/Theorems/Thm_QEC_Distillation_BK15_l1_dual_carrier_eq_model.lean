-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_model
-- name    : QEC.Distillation.BK15.l1_dual_carrier_eq_model
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:39.480828+00:00
-- url     : https://prove2.me/theorems/849ee90d-521b-4705-add2-7946ec072ce4
-- title:
--   BK15: l1 dual carrier eq model
-- statement:
--   The source relation `L1⊥ = L2 ⊕ [1]`, in a concrete injective presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L332-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L332-L336

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_dual_carrier_eq_model : L1.dual.carrier = L1DualModel.carrier := by sorry

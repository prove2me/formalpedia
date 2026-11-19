-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_model
-- name    : QEC.Distillation.BK15.l2_dual_carrier_eq_model
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:48.898774+00:00
-- url     : https://prove2.me/theorems/870fdc31-a60c-4fda-9133-4987037577f4
-- title:
--   BK15: l2 dual carrier eq model
-- statement:
--   The source relation `L2⊥ = L1 ⊕ [1]`, in a concrete injective presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L339-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L339-L343

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_dual_carrier_eq_model : L2.dual.carrier = L2DualModel.carrier := by sorry

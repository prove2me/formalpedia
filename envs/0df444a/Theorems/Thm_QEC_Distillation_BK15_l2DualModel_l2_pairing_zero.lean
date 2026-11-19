-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2DualModel_l2_pairing_zero
-- name    : QEC.Distillation.BK15.l2DualModel_l2_pairing_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:54:03.348458+00:00
-- url     : https://prove2.me/theorems/1229859e-96b0-4164-9b69-3ff22bdfcdb3
-- title:
--   BK15: l2 Dual Model l2 pairing zero
-- statement:
--   The explicit `L1 ⊕ [1]` model is orthogonal to `L2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L310-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L310-L313

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2DualModel_l2_pairing_zero :
    ∀ (ac : (Fin 4 → Bit) × Bit) (b : Sum (Fin 4) QuadraticIndex → Bit),
      wordPairing (l2DualCoefficientMap ac) (l2CoefficientMap b) = 0 := by sorry

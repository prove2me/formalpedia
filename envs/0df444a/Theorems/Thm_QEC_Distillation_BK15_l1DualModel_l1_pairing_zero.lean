-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1DualModel_l1_pairing_zero
-- name    : QEC.Distillation.BK15.l1DualModel_l1_pairing_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:53:58.41877+00:00
-- url     : https://prove2.me/theorems/9cf247d4-6cd8-4121-99e5-6f755d140e85
-- title:
--   BK15: l1 Dual Model l1 pairing zero
-- statement:
--   The explicit `L2 ⊕ [1]` model is orthogonal to `L1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L298-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L298-L301

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1DualModel_l1_pairing_zero :
    ∀ (bc : (Sum (Fin 4) QuadraticIndex → Bit) × Bit) (a : Fin 4 → Bit),
      wordPairing (l1DualCoefficientMap bc) (l1CoefficientMap a) = 0 := by sorry

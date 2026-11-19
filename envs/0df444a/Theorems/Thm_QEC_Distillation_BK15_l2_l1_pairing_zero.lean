-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_l1_pairing_zero
-- name    : QEC.Distillation.BK15.l2_l1_pairing_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:53:21.224959+00:00
-- url     : https://prove2.me/theorems/c0305c78-ec14-45e1-9d6b-fdb9cf49eac4
-- title:
--   BK15: l2 l1 pairing zero
-- statement:
--   Every `L2` generator is orthogonal to every `L1` generator combination.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L267-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L267-L270

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_l1_pairing_zero :
    ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by sorry

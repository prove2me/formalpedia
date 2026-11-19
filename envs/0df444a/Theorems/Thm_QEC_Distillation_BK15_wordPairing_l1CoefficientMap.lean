-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_wordPairing_l1CoefficientMap
-- name    : QEC.Distillation.BK15.wordPairing_l1CoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:55:16.605465+00:00
-- url     : https://prove2.me/theorems/93ad6fc3-9d5f-4a3f-ad11-f17b1e1cfed3
-- title:
--   BK15: word Pairing l1 Coefficient Map
-- statement:
--   Pairing against an `L1` word is the corresponding finite generator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L422-L425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L422-L425

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.wordPairing_l1CoefficientMap (w : Word) (a : Fin 4 → Bit) :
    wordPairing w (l1CoefficientMap a) =
      ∑ j : Fin 4, a j • wordPairing w (linearGenerator j) := by sorry

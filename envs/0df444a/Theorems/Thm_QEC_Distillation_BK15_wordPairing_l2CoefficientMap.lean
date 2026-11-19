-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_wordPairing_l2CoefficientMap
-- name    : QEC.Distillation.BK15.wordPairing_l2CoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:55:27.995736+00:00
-- url     : https://prove2.me/theorems/c30c8811-cc8d-4742-81df-ac8180c4f63d
-- title:
--   BK15: word Pairing l2 Coefficient Map
-- statement:
--   Pairing against an `L2` word is the corresponding finite generator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L428-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L428-L432

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.wordPairing_l2CoefficientMap (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) :
    wordPairing w (l2CoefficientMap b) =
      ∑ g : Sum (Fin 4) QuadraticIndex, b g • wordPairing w (l2Generator g) := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2Syndrome_zero_pairing
-- name    : QEC.Distillation.BK15.l2Syndrome_zero_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:56:06.312947+00:00
-- url     : https://prove2.me/theorems/4b8b10db-e0b3-456b-9355-34edcaff699f
-- title:
--   BK15: l2 Syndrome zero pairing
-- statement:
--   The BK15 construction uses the l2 Syndrome zero pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L443-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L443-L451

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2Syndrome_zero_pairing (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit)
    (hzero : l2Syndrome w = 0) : wordPairing w (l2CoefficientMap b) = 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1Syndrome_zero_pairing
-- name    : QEC.Distillation.BK15.l1Syndrome_zero_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:55:32.699147+00:00
-- url     : https://prove2.me/theorems/c535fe07-0d49-4d6c-8ff4-03d98a251e25
-- title:
--   BK15: l1 Syndrome zero pairing
-- statement:
--   The BK15 construction uses the l1 Syndrome zero pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L434-L441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L434-L441

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1Syndrome_zero_pairing (w : Word) (a : Fin 4 → Bit)
    (hzero : l1Syndrome w = 0) : wordPairing w (l1CoefficientMap a) = 0 := by sorry

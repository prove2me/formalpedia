-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1DualWords_card
-- name    : QEC.Distillation.BK15.l1DualWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:05:08.618953+00:00
-- url     : https://prove2.me/theorems/9615e023-889c-4197-86dc-d8d1bc3259e0
-- title:
--   BK15: l1 Dual Words card
-- statement:
--   The BK15 construction uses the l1 Dual Words card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L549-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L549-L551

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1DualWords_card : l1DualWords.card = 2048 := by sorry

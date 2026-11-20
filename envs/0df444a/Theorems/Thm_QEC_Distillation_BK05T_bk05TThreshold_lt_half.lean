-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TThreshold_lt_half
-- name    : QEC.Distillation.BK05T.bk05TThreshold_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:08.272238+00:00
-- url     : https://prove2.me/theorems/cb75ea0a-2424-4821-972d-5c2b910dc5eb
-- title:
--   BK05 T: bk05 TThreshold lt half
-- statement:
--   The BK05 T construction uses the bk05 TThreshold lt half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L56-L60

import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TThreshold_lt_half : ((1 - Real.sqrt (3 / 7 : Real)) / 2) < 1 / 2 := by sorry

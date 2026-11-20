-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_lt_input
-- name    : QEC.Distillation.BK05T.bk05TRecurrence_lt_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:45.720372+00:00
-- url     : https://prove2.me/theorems/8f2fb8e6-d169-4670-8b5a-4ebcdb4b0bbf
-- title:
--   BK05 T: bk05 TRecurrence lt input
-- statement:
--   The BK05 T construction uses the bk05 TRecurrence lt input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L218-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L218-L233

import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TRecurrence_lt_input (epsilon : Real) (hzero : 0 < epsilon) (hthreshold : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) : (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o)) < epsilon := by sorry

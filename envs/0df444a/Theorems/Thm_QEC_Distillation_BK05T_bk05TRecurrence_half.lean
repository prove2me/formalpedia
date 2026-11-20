-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_half
-- name    : QEC.Distillation.BK05T.bk05TRecurrence_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:17:46.889685+00:00
-- url     : https://prove2.me/theorems/95c21332-85c2-4b70-8f63-ffa90f96b794
-- title:
--   BK05 T: bk05 TRecurrence half
-- statement:
--   The BK05 T construction uses the bk05 TRecurrence half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L239-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L239-L241

import Mathlib.Data.Real.Basic
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TRecurrence_half : (let epsilon : Real := (1 / 2 : Real); (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o))) = (1 / 2 : Real) := by sorry

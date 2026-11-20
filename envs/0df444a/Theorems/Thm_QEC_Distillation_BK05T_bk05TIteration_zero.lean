-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TIteration_zero
-- name    : QEC.Distillation.BK05T.bk05TIteration_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:43:56.890147+00:00
-- url     : https://prove2.me/theorems/5842f272-9a9a-4929-9127-31f721038e77
-- title:
--   BK05 T: bk05 TIteration zero
-- statement:
--   The BK05 T construction uses the bk05 TIteration zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L312-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L312-L313

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TIteration_zero (epsilon : Real) :
  Nat.iterate (fun input : Real =>
      let z : Real := (input ^ 5 + 5 * input ^ 2 * (1 - input) ^ 3) / 6
      let o : Real := ((1 - input) ^ 5 + 5 * input ^ 3 * (1 - input) ^ 2) / 6
      z / (z + o)) 0 epsilon = epsilon := by sorry

attribute [defeq] QEC.Distillation.BK05T.bk05TIteration_zero

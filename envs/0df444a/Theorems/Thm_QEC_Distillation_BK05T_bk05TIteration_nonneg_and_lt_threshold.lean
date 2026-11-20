-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TIteration_nonneg_and_lt_threshold
-- name    : QEC.Distillation.BK05T.bk05TIteration_nonneg_and_lt_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:19:39.890229+00:00
-- url     : https://prove2.me/theorems/d5916cf7-68a5-42d6-8828-5b1981a48b29
-- title:
--   BK05 T: bk05 TIteration nonneg and lt threshold
-- statement:
--   The BK05 T construction uses the bk05 TIteration nonneg and lt threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L320-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L320-L337

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TIteration_nonneg_and_lt_threshold (epsilon : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) (rounds : Nat) :
    let f : Real → Real := (fun input : Real =>
      let z : Real := (input ^ 5 + 5 * input ^ 2 * (1 - input) ^ 3) / 6
      let o : Real := ((1 - input) ^ 5 + 5 * input ^ 3 * (1 - input) ^ 2) / 6
      z / (z + o))
    0 <= Nat.iterate f rounds epsilon ∧ Nat.iterate f rounds epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2) := by sorry

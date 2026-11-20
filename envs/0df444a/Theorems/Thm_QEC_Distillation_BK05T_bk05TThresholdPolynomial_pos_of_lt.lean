-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TThresholdPolynomial_pos_of_lt
-- name    : QEC.Distillation.BK05T.bk05TThresholdPolynomial_pos_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:50.925639+00:00
-- url     : https://prove2.me/theorems/ef10de64-f1f2-4564-8545-9e65d36c6e60
-- title:
--   BK05 T: bk05 TThreshold Polynomial pos of lt
-- statement:
--   The BK05 T construction uses the bk05 TThreshold Polynomial pos of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L70-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L70-L90

import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false

theorem QEC.Distillation.BK05T.bk05TThresholdPolynomial_pos_of_lt (epsilon : Real) (hepsilon : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) : 0 < 7 * epsilon ^ 2 - 7 * epsilon + 1 := by sorry

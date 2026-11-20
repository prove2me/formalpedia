-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_sub_input
-- name    : QEC.Distillation.BK05T.bk05TRecurrence_sub_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:41:39.123907+00:00
-- url     : https://prove2.me/theorems/99c763ce-0f43-4225-ba48-7b3765f3ebc6
-- title:
--   BK05 T: bk05 TRecurrence sub input
-- statement:
--   The BK05 T construction uses the bk05 TRecurrence sub input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L205-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L205-L216

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.bk05TRecurrence_sub_input
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon - epsilon =
      -(epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
          bk05TThresholdPolynomial epsilon) /
        (6 * fiveQubitSuccessProbability epsilon) := by sorry

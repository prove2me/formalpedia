-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_eq_oddsFormula
-- name    : QEC.Distillation.BK05T.bk05TRecurrence_eq_oddsFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:44:32.751188+00:00
-- url     : https://prove2.me/theorems/bf389a6d-4663-4b9e-a492-8a527c7a9f8c
-- title:
--   BK05 T: bk05 TRecurrence eq odds Formula
-- statement:
--   The BK05 T construction uses the bk05 TRecurrence eq odds Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L187-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L187-L203

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.bk05TRecurrence_eq_oddsFormula
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon =
      (bk05TOdds epsilon ^ 5 + 5 * bk05TOdds epsilon ^ 2) /
        (1 + 5 * bk05TOdds epsilon ^ 2 +
          5 * bk05TOdds epsilon ^ 3 + bk05TOdds epsilon ^ 5) := by sorry

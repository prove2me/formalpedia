-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_fixed_iff
-- name    : QEC.Distillation.BK05T.bk05TRecurrence_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:50:21.261884+00:00
-- url     : https://prove2.me/theorems/5e4de211-e6e1-4549-871b-a07be783d34b
-- title:
--   BK05 T: bk05 TRecurrence fixed iff
-- statement:
--   The BK05 T construction uses the bk05 TRecurrence fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L276-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L276-L303

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.bk05TRecurrence_fixed_iff
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon = epsilon <->
      epsilon = 0 \/ epsilon = bk05TThreshold \/ epsilon = 1 / 2 := by sorry

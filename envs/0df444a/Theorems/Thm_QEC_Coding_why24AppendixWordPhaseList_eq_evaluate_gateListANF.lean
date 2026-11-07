-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_evaluate_gateListANF
-- name    : QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gateListANF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:25.78277+00:00
-- url     : https://prove2.me/theorems/1daffbe3-f43e-4965-9aff-6f8b59541204
-- title:
--   Coding: why24 Appendix Word Phase List eq evaluate gate List ANF
-- statement:
--   The Coding construction uses the why24 Appendix Word Phase List eq evaluate gate List ANF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L184-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L184-L203

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF

theorem QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gateListANF
    (gates : List Why24AppendixGate) (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList gates word =
      evaluate word (why24AppendixGateListANF gates) := by sorry

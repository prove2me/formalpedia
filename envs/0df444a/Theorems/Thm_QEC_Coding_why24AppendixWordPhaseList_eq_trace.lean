-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_trace
-- name    : QEC.Coding.why24AppendixWordPhaseList_eq_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:52:44.790809+00:00
-- url     : https://prove2.me/theorems/963e884f-ef07-4971-9ee9-aaa36ca6aa7c
-- title:
--   Coding: why24 Appendix Word Phase List eq trace
-- statement:
--   The literal Appendix-A phase fold equals the concrete selected-basis
--   seventh-power trace for every Boolean word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L216-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L216-L223

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF

theorem QEC.Coding.why24AppendixWordPhaseList_eq_trace
    (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList why24AppendixGateList word =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by sorry

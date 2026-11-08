-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
-- name    : QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:59.674115+00:00
-- url     : https://prove2.me/theorems/3c2d2c7f-1ddf-4dee-ba04-21f1aad21516
-- title:
--   Coding: why24 Appendix Word Phase List eq evaluate gate Phase Polynomial
-- statement:
--   The literal Appendix-A phase fold is evaluation of the certified target
--   sparse polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L207-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L207-L212

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF

theorem QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
    (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList why24AppendixGateList word =
      evaluate word gatePhasePolynomial := by sorry

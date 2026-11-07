-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_selectedANFWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedANFWord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:36:48.236801+00:00
-- url     : https://prove2.me/theorems/b5d322b5-68d9-45f4-84bc-9572f64adac7
-- title:
--   Why24 Appendix ANF: polynomial Eval evaluate selected ANFWord
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval evaluate selected ANFWord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L71-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L71-L76

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedANFWord (word : Word) :
    polynomialEval (fun power => evaluate word (selectedANFWord power)) =
      f1024SelectedCoordinates.symm word := by sorry

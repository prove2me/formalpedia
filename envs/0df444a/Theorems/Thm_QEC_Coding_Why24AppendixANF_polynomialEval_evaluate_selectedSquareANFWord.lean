-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_selectedSquareANFWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedSquareANFWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:51:06.342314+00:00
-- url     : https://prove2.me/theorems/972a9987-3a1c-4138-a1bc-4c346783ffbe
-- title:
--   Why24 Appendix ANF: polynomial Eval evaluate selected Square ANFWord
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval evaluate selected Square ANFWord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L78-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L78-L83

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedSquareANFWord (word : Word) :
    polynomialEval (fun power => evaluate word (selectedSquareANFWord power)) =
      (f1024SelectedCoordinates.symm word) ^ 2 := by sorry

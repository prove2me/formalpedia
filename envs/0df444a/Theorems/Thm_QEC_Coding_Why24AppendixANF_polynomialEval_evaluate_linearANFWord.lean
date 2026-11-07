-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_linearANFWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_linearANFWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:42:25.720251+00:00
-- url     : https://prove2.me/theorems/927dbfdd-e518-4db5-8fa1-86b178a6de28
-- title:
--   Why24 Appendix ANF: polynomial Eval evaluate linear ANFWord
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval evaluate linear ANFWord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L28-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L28-L43

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_linearANFWord
    (word : Word) (basisWords : Fin 10 → Word) :
    polynomialEval
        (fun power => evaluate word (linearANFWord basisWords power)) =
      ∑ selected : Fin 10, word selected • polynomialEval (basisWords selected) := by sorry

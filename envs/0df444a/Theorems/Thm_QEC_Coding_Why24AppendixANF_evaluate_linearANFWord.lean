-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_evaluate_linearANFWord
-- name    : QEC.Coding.Why24AppendixANF.evaluate_linearANFWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:51:11.072072+00:00
-- url     : https://prove2.me/theorems/d728da68-b9ff-48b2-9321-39fc66494fd3
-- title:
--   Why24 Appendix ANF: evaluate linear ANFWord
-- statement:
--   The Why24 Appendix ANF construction uses the evaluate linear ANFWord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L19-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L19-L26

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.evaluate_linearANFWord (word : Word) (basisWords : Fin 10 → Word)
    (power : Fin 10) :
    evaluate word (linearANFWord basisWords power) =
      ∑ selected : Fin 10, basisWords selected power * word selected := by sorry

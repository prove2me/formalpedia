-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_wordMul
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_wordMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:52:19.92741+00:00
-- url     : https://prove2.me/theorems/69b22327-5c59-40b1-890f-989d0e1b322f
-- title:
--   Why24 Appendix ANF: polynomial Eval word Mul
-- statement:
--   The coordinate multiplication table implements multiplication in
--   `F1024`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L246-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L246-L266

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.polynomialEval_wordMul (left right : Word) :
    polynomialEval (wordMul left right) =
      polynomialEval left * polynomialEval right := by sorry

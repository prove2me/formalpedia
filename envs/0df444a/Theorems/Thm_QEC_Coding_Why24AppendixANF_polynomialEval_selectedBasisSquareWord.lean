-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisSquareWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisSquareWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:36.906132+00:00
-- url     : https://prove2.me/theorems/8331d055-485a-4869-b0d7-b606e7e85ab0
-- title:
--   Why24 Appendix ANF: polynomial Eval selected Basis Square Word
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval selected Basis Square Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L285-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L285-L290

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisSquareWord (selected : Fin 10) :
    polynomialEval (selectedBasisSquareWord selected) =
      f1024SelectedSelfDualBasis selected ^ 2 := by sorry

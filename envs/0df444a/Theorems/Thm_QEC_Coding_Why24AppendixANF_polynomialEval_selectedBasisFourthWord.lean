-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisFourthWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisFourthWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:37:59.492447+00:00
-- url     : https://prove2.me/theorems/f3ee77af-ee2d-40f3-a3ab-3e2670adcd84
-- title:
--   Why24 Appendix ANF: polynomial Eval selected Basis Fourth Word
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval selected Basis Fourth Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L292-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L292-L297

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisFourthWord (selected : Fin 10) :
    polynomialEval (selectedBasisFourthWord selected) =
      f1024SelectedSelfDualBasis selected ^ 4 := by sorry

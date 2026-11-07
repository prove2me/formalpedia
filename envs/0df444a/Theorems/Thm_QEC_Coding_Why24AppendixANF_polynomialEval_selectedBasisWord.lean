-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisWord
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:08:32.687787+00:00
-- url     : https://prove2.me/theorems/251a5ed1-6358-4bbe-8c29-a41b694df3ad
-- title:
--   Why24 Appendix ANF: polynomial Eval selected Basis Word
-- statement:
--   A selected-basis coordinate column evaluates to the corresponding actual
--   self-dual basis element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L270-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L270-L283

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisWord (selected : Fin 10) :
    polynomialEval (selectedBasisWord selected) =
      f1024SelectedSelfDualBasis selected := by sorry

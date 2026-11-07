-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_single
-- name    : QEC.Coding.Why24AppendixANF.polynomialEval_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:06:47.736913+00:00
-- url     : https://prove2.me/theorems/4db6a446-d993-47cd-a98f-2d5f01480d87
-- title:
--   Why24 Appendix ANF: polynomial Eval single
-- statement:
--   The Why24 Appendix ANF construction uses the polynomial Eval single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L32-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L32-L43

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.polynomialEval_single (coordinate : Fin 10) :
    polynomialEval (Pi.single coordinate (1 : ZMod 2)) =
      f1024Alpha ^ (coordinate : Nat) := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_alphaReduction_eval
-- name    : QEC.Coding.Why24AppendixANF.alphaReduction_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:59.701456+00:00
-- url     : https://prove2.me/theorems/f6e436af-4529-4e05-838b-b916dbd83154
-- title:
--   Why24 Appendix ANF: alpha Reduction eval
-- statement:
--   Every row of the fixed reduction table evaluates to its represented
--   power of `f1024Alpha`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L212-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L212-L233

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.alphaReduction_eval (power : Fin 19) :
    polynomialEval (alphaReduction power) = f1024Alpha ^ (power : Nat) := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator
-- name    : QEC.Coding.Why24AppendixANF.generator_mul_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:42:05.791818+00:00
-- url     : https://prove2.me/theorems/9d8bf0b4-d587-4044-a879-fc66c58ddcce
-- title:
--   Why24 Appendix ANF: generator mul generator
-- statement:
--   The Why24 Appendix ANF construction uses the generator mul generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L19-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L19-L28

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.generator_mul_generator (left right : Fin 10) :
    generator left * generator right =
      MonoidAlgebra.single ⟨{left, right}⟩ 1 := by sorry

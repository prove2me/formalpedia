-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator_mul_generator
-- name    : QEC.Coding.Why24AppendixANF.generator_mul_generator_mul_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:43:17.825025+00:00
-- url     : https://prove2.me/theorems/c295c674-ae8a-463e-ae6f-4e41979a33d2
-- title:
--   Why24 Appendix ANF: generator mul generator mul generator
-- statement:
--   The Why24 Appendix ANF construction uses the generator mul generator mul generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L30-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L30-L40

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.generator_mul_generator_mul_generator
    (first second third : Fin 10) :
    generator first * generator second * generator third =
      MonoidAlgebra.single ⟨{first, second, third}⟩ 1 := by sorry

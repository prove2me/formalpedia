-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurent_sum_C_mul_T_eq
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurent_sum_C_mul_T_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:04.202223+00:00
-- url     : https://prove2.me/theorems/d3b1c3a4-c853-47ca-a36a-e5b5f0779592
-- title:
--   Laurent Finite Window: laurent sum C mul T eq
-- statement:
--   The Laurent Finite Window construction uses the laurent sum C mul T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L70-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L70-L74

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurent_sum_C_mul_T_eq (f : LaurentPolynomial k) :
    f.coeff.support.sum (fun n : ℤ =>
      LaurentPolynomial.C (R := k) (f.coeff n) * LaurentPolynomial.T (R := k) n) = f := by sorry

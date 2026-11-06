-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_inverse_X_pow
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_inverse_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:29:32.937476+00:00
-- url     : https://prove2.me/theorems/58fa8871-3f42-4140-b689-43911b547070
-- title:
--   Laurent Finite Window: direct inverse X pow
-- statement:
--   The Laurent Finite Window construction uses the direct inverse X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L31-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L31-L42

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_inverse_X_pow (m n : ℕ) :
    directCoordinate k (Polynomial.X ^ m) * inverseCoordinate k (Polynomial.X ^ n) =
      LaurentPolynomial.T (R := k) ((m : ℤ) - n) := by sorry

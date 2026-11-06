-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_coeff
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:07:30.131361+00:00
-- url     : https://prove2.me/theorems/5a2efa30-7208-4f74-b255-0fc985d472ef
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients coeff
-- statement:
--   The constructed reflection has exactly the reflected inner coefficient at every outer index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L25-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L25-L27

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_coeff (m : ℕ) (Φ : Polynomial (Polynomial k)) (i : ℕ) :
    (reflectCoefficients m Φ).coeff i = (Φ.coeff i).reflect m := by sorry

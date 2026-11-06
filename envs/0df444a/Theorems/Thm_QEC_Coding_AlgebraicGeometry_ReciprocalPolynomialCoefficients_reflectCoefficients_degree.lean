-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_degree
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:07:50.722904+00:00
-- url     : https://prove2.me/theorems/0c5a4ee2-3cd0-4e51-bc73-a156003c79ec
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients degree
-- statement:
--   Inner reflection cannot increase the degree in the unchanged outer variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L30-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L30-L35

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_degree (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : Φ.natDegree ≤ r) : (reflectCoefficients m Φ).natDegree ≤ r := by sorry

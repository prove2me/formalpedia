-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_monic
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:24.303479+00:00
-- url     : https://prove2.me/theorems/b9a9dd4d-aed5-42db-9bff-75cd3f1dbe7e
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients monic
-- statement:
--   The reflected top coefficient of a common-power leading term is one, so the outer polynomial is monic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L61-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L61-L68

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_monic (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hdegree : Φ.natDegree ≤ r)
    (htop : Φ.coeff r = Polynomial.X^m) :
    (reflectCoefficients m Φ).Monic := by sorry

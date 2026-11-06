-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_map
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:07:54.455253+00:00
-- url     : https://prove2.me/theorems/855ca7e3-664a-426e-a87a-be1c2839d377
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients map
-- statement:
--   At reciprocal nonzero coordinates, the reflected coefficient evaluation recovers the original polynomial after multiplying by the common power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L38-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L38-L47

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : k) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.evalRingHom z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.evalRingHom z) := by sorry

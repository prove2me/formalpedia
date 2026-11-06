-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_map_field
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map_field
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:07:54.935417+00:00
-- url     : https://prove2.me/theorems/7ab60dab-d547-4646-8eae-18200b959a9f
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients map field
-- statement:
--   The common-power reflection identity also holds after an actual coefficient field map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L72-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L72-L82

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map_field {L : Type*} [Field L]
    (φ : k →+* L) (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : L) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.eval₂RingHom φ z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.eval₂RingHom φ z) := by sorry

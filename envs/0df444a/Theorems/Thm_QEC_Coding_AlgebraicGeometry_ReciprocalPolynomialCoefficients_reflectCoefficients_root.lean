-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_root
-- name    : QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:22.179734+00:00
-- url     : https://prove2.me/theorems/d900a710-48e1-4536-83cc-1f0583a2a7b7
-- title:
--   Reciprocal Polynomial Coefficients: reflect Coefficients root
-- statement:
--   The genuine reciprocal reflection identity transports an actual scalar root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L50-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean#L50-L58

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z t : k) (hz : z ≠ 0)
    (ht : Φ.eval₂ (Polynomial.evalRingHom z) t = 0) :
    (reflectCoefficients m Φ).eval₂ (Polynomial.evalRingHom z⁻¹) t = 0 := by sorry

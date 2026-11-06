-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_trace_weighted_diagonal_mul
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_weighted_diagonal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:02.36855+00:00
-- url     : https://prove2.me/theorems/aa90c0cd-7b41-4208-be57-0b5e26678e4b
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation trace weighted diagonal mul
-- statement:
--   The weighted logarithmic derivative of a diagonal matrix followed by a
--   change-of-basis matrix splits into a diagonal term and a change-of-basis
--   term.  The conjugated weight on the diagonal side is supplied explicitly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L34-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L34-L66

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_weighted_diagonal_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k₀ K K)
    (Gt Gs P A Ainv Q : Matrix n n K)
    (hAinvA : Ainv * A = 1)
    (hconj : Q * Gt * P = Gs) :
    Matrix.trace
        (Gt * P * Ainv * entrywiseMatrixDerivation D (A * Q)) =
      Matrix.trace (Gs * Ainv * entrywiseMatrixDerivation D A) +
        Matrix.trace ((Gt * P) * entrywiseMatrixDerivation D Q) := by sorry

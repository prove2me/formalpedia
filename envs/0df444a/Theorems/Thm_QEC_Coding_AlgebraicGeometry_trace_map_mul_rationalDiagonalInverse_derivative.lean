-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_trace_map_mul_rationalDiagonalInverse_derivative
-- name    : QEC.Coding.AlgebraicGeometry.trace_map_mul_rationalDiagonalInverse_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:07.415037+00:00
-- url     : https://prove2.me/theorems/2437f4dd-7066-470b-9f3e-b9ab525bc212
-- title:
--   Algebraic Geometry: trace map mul rational Diagonal Inverse derivative
-- statement:
--   The weighted diagonal matrix logarithmic trace is the finite sum of its
--   diagonal scalar logarithmic terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L49-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L49-L71

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.trace_map_mul_rationalDiagonalInverse_derivative
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n k[X]) (a : n → k[X]) :
    Matrix.trace
        (((algebraMap k[X] (RatFunc k)).mapMatrix R *
            rationalDiagonalMatrixInverse a) *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix
              (Matrix.diagonal a))) =
      ∑ i, algebraMap k[X] (RatFunc k) (R i i) *
        (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
          algebraMap k[X] (RatFunc k) (a i).derivative := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_trace_map_mul_entrywiseMatrixDerivation_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.trace_map_mul_entrywiseMatrixDerivation_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:04.804203+00:00
-- url     : https://prove2.me/theorems/8b15d8fb-60bf-484d-8c11-c052790aeae1
-- title:
--   Algebraic Geometry: trace map mul entrywise Matrix Derivation polynomial
-- statement:
--   A polynomial change-of-basis logarithmic trace term remains polynomial
--   after mapping to the rational function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L78-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L78-L94

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.trace_map_mul_entrywiseMatrixDerivation_polynomial
    {n : Type*} [Fintype n] [DecidableEq n]
    (Pinv P : Matrix n n k[X]) :
    Matrix.trace
        ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix P)) =
      algebraMap k[X] (RatFunc k)
        (Matrix.trace (Pinv * entrywisePolynomialDerivative P)) := by sorry

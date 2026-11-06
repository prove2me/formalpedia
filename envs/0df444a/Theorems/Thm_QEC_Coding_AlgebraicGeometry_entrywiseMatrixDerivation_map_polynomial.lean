-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_map_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_map_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:42.056822+00:00
-- url     : https://prove2.me/theorems/c13dc432-e6e1-44ef-929e-836457a8f73b
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation map polynomial
-- statement:
--   Mapping a polynomial matrix into the rational function field commutes
--   with entrywise differentiation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L62-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L62-L74

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_map_polynomial {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n k[X]) :
    entrywiseMatrixDerivation
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1)
        ((algebraMap k[X] (RatFunc k)).mapMatrix A) =
      (algebraMap k[X] (RatFunc k)).mapMatrix
        (entrywisePolynomialDerivative A) := by sorry

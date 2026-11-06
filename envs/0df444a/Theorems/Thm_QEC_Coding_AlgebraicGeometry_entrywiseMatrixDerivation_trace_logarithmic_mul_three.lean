-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_trace_logarithmic_mul_three
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_logarithmic_mul_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:33.617618+00:00
-- url     : https://prove2.me/theorems/1dd36c3a-809a-4139-a9af-c3d4d6813906
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation trace logarithmic mul three
-- statement:
--   The trace of the logarithmic derivative of a three-factor matrix product
--   splits into the three factor contributions.  Only the inverse-side identities
--   actually used by the cyclic trace calculation are assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L105-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L105-L189

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_logarithmic_mul_three
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k K K)
    (P Pinv A Ainv Q Qinv : Matrix n n K)
    (hPinvP : Pinv * P = 1)
    (hAinvA : Ainv * A = 1) (hAAinv : A * Ainv = 1)
    (hQQinv : Q * Qinv = 1) :
    Matrix.trace
        (Qinv * Ainv * Pinv *
          entrywiseMatrixDerivation D (P * A * Q)) =
      Matrix.trace (Pinv * entrywiseMatrixDerivation D P) +
        Matrix.trace (Ainv * entrywiseMatrixDerivation D A) +
          Matrix.trace (Qinv * entrywiseMatrixDerivation D Q) := by sorry

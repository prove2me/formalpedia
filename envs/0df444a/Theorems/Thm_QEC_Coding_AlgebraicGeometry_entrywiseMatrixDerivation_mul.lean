-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_mul
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:58.731373+00:00
-- url     : https://prove2.me/theorems/f2e47e9b-18de-4936-a59e-b5b57fb8b549
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation mul
-- statement:
--   Entrywise differentiation obeys the matrix Leibniz rule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L46-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L46-L60

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_mul {m n p : Type*} [Fintype n]
    (D : Derivation k K K) (A : Matrix m n K) (B : Matrix n p K) :
    entrywiseMatrixDerivation D (A * B) =
      entrywiseMatrixDerivation D A * B +
        A * entrywiseMatrixDerivation D B := by sorry

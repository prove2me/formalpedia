-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_inverse
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:27.623701+00:00
-- url     : https://prove2.me/theorems/4bdc977d-4a4f-4c41-80d9-25919ed4788a
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation inverse
-- statement:
--   If two square matrices are mutual inverses, differentiating either
--   inverse relation gives the usual inverse rule entrywise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L76-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L76-L100

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_inverse {n : Type*} [Fintype n]
    [DecidableEq n] (D : Derivation k K K) (A U : Matrix n n K)
    (hAU : A * U = 1) (hUA : U * A = 1) :
    entrywiseMatrixDerivation D U =
      -(U * entrywiseMatrixDerivation D A * U) := by sorry

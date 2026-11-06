-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
-- name    : QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:51.195662+00:00
-- url     : https://prove2.me/theorems/2e45b887-2aa6-42db-abdd-5441546dc317
-- title:
--   Algebraic Geometry: entrywise Matrix Derivation apply
-- statement:
--   The Algebraic Geometry construction uses the entrywise Matrix Derivation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L32-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean#L32-L35

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply {m n : Type*}
    (D : Derivation k K K) (A : Matrix m n K) (i : m) (j : n) :
    entrywiseMatrixDerivation D A i j = D (A i j) := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply

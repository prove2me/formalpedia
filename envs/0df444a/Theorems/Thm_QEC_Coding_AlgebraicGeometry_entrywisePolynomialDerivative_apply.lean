-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
-- name    : QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:40.127376+00:00
-- url     : https://prove2.me/theorems/913e54f2-340f-4141-8fc6-4ff3a93b52dd
-- title:
--   Algebraic Geometry: entrywise Polynomial Derivative apply
-- statement:
--   The Algebraic Geometry construction uses the entrywise Polynomial Derivative apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L34-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L34-L37

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply {m n : Type*}
    (A : Matrix m n k[X]) (i : m) (j : n) :
    entrywisePolynomialDerivative A i j = (A i j).derivative := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply

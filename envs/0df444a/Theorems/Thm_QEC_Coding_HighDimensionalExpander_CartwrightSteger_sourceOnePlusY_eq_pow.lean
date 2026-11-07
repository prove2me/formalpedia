-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceOnePlusY_eq_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceOnePlusY_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:38:10.097083+00:00
-- url     : https://prove2.me/theorems/39ea1fc3-943c-495b-9893-c94a4840ac17
-- title:
--   Cartwright Steger: source One Plus Y eq pow
-- statement:
--   For the explicit choice `beta = 1`, the relative norm defining the source
--   coordinate is the `d`-th power of `1 + X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L242-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L242-L245

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceOnePlusY_eq_pow (P : BasePrime) (r : Rank) :
    sourceOnePlusY P r =
      (1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank := by sorry

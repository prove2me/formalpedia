-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceYPolynomial_eq_pow_sub_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_eq_pow_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:38:01.333974+00:00
-- url     : https://prove2.me/theorems/7f5a4470-220f-46f4-b498-b1c57958c2c8
-- title:
--   Cartwright Steger: source YPolynomial eq pow sub one
-- statement:
--   The Cartwright Steger construction uses the source YPolynomial eq pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L247-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L247-L250

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_eq_pow_sub_one (P : BasePrime) (r : Rank) :
    sourceYPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank - 1 := by sorry

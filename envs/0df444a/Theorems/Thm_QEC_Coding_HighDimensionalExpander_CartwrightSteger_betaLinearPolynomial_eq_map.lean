-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_betaLinearPolynomial_eq_map
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.betaLinearPolynomial_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:10.041245+00:00
-- url     : https://prove2.me/theorems/e32b10d3-5eae-4e93-913f-8c9bff9372dc
-- title:
--   Cartwright Steger: beta Linear Polynomial eq map
-- statement:
--   The Cartwright Steger construction uses the beta Linear Polynomial eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L223-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L223-L227

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.betaLinearPolynomial_eq_map (P : BasePrime) (r : Rank) :
    betaLinearPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P).map
        (algebraMap (BaseField P) (ConstantExtension P r)) := by sorry

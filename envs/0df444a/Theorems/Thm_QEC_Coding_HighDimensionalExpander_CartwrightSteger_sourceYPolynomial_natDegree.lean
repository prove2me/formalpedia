-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceYPolynomial_natDegree
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:30.653309+00:00
-- url     : https://prove2.me/theorems/eac46894-9869-43a7-84d1-53fe9ef820d9
-- title:
--   Cartwright Steger: source YPolynomial nat Degree
-- statement:
--   The LSV substitution polynomial has exactly the matrix rank as its
--   degree; consequently every fiber has at most `d` elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L254-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L254-L276

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_natDegree (P : BasePrime) (r : Rank) :
    (sourceYPolynomial P r).natDegree = r.matrixRank := by sorry

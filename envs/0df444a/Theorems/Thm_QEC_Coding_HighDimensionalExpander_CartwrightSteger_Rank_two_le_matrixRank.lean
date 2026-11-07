-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.two_le_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:40.389496+00:00
-- url     : https://prove2.me/theorems/520e1dae-15b1-4bb1-8b41-be67b2044bdf
-- title:
--   Rank: two le matrix Rank
-- statement:
--   The Rank construction uses the two le matrix Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L78-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L78-L79

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
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.two_le_matrixRank (r : Rank) : 2 <= r.matrixRank := by sorry

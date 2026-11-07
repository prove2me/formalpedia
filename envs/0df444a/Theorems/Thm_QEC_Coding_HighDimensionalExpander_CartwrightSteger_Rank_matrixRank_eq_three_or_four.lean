-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_matrixRank_eq_three_or_four
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.matrixRank_eq_three_or_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:39.880169+00:00
-- url     : https://prove2.me/theorems/629af562-4c65-4fb5-9d23-5675353c4f86
-- title:
--   Rank: matrix Rank eq three or four
-- statement:
--   The Rank construction uses the matrix Rank eq three or four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L74-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L74-L76

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.matrixRank_eq_three_or_four (r : Rank) :
    r.matrixRank = 3 \/ r.matrixRank = 4 := by sorry

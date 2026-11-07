-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueField_unbounded
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueField_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:33.626191+00:00
-- url     : https://prove2.me/theorems/145711ea-2d36-4ed8-9d0f-2eac6b7873e4
-- title:
--   Cartwright Steger: residue Field unbounded
-- statement:
--   The Cartwright Steger construction uses the residue Field unbounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L302-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L302-L315

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueField_unbounded (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (ResidueField P r level) := by sorry

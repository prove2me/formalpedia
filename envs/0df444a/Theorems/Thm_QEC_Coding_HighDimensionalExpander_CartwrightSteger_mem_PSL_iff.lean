-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_PSL_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_PSL_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:24.682301+00:00
-- url     : https://prove2.me/theorems/bf4f57cb-e3bf-4167-8329-bda66e31da07
-- title:
--   Cartwright Steger: mem PSL iff
-- statement:
--   The Cartwright Steger construction uses the mem PSL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L333-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L333-L338

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_PSL_iff (P : BasePrime) (r : Rank) (level : Nat)
    (g : PGL P r level) :
    g ∈ PSL P r level ↔
      ∃ s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level), specialToProjective P r level s = g := by sorry

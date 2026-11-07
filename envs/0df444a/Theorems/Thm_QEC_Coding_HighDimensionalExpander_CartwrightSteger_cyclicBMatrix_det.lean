-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicBMatrix_det
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicBMatrix_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:14.075201+00:00
-- url     : https://prove2.me/theorems/302ec69d-6011-47d7-a99a-7f04414d641e
-- title:
--   Cartwright Steger: cyclic BMatrix det
-- statement:
--   The Cartwright Steger construction uses the cyclic BMatrix det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L138-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L138-L143

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicBMatrix_det {K : Type*} [Field K]
    (r : Rank) (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det (cyclicBMatrix r y) = y / (1 + y) := by sorry

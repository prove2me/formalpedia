-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:05.495451+00:00
-- url     : https://prove2.me/theorems/b2f4958f-e929-4e82-9c0c-8c0080157e30
-- title:
--   Cartwright Steger: cartwright Steger Norm Unit coe
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Norm Unit coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L164-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L164-L167

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe (P : BasePrime) (r : Rank) :
    (cartwrightStegerNormUnit P r : SplittingFunctionField P r) =
      splittingY P r / (1 + splittingY P r) := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe

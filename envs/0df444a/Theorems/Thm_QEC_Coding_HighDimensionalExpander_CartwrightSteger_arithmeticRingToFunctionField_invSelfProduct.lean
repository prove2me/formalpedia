-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_invSelfProduct
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_invSelfProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:22:42.006576+00:00
-- url     : https://prove2.me/theorems/01116bb7-52d0-4174-bed8-19008efa2c8f
-- title:
--   Cartwright Steger: arithmetic Ring To Function Field inv Self Product
-- statement:
--   The Cartwright Steger construction uses the arithmetic Ring To Function Field inv Self Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L234-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean#L234-L245

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_invSelfProduct
    (P : BasePrime) :
    arithmeticRingToFunctionField P
        (IsLocalization.Away.invSelf
          (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)) =
      (RatFunc.X * (1 + RatFunc.X))⁻¹ := by sorry

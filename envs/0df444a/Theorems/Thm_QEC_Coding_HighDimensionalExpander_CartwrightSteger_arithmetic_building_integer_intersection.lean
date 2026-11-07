-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmetic_building_integer_intersection
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmetic_building_integer_intersection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:42.495857+00:00
-- url     : https://prove2.me/theorems/73349da2-9985-4b8a-b565-af26afcd495a
-- title:
--   Cartwright Steger: arithmetic building integer intersection
-- statement:
--   The Cartwright Steger construction uses the arithmetic building integer intersection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L169-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L169-L191

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmetic_building_integer_intersection
    (P : BasePrime) (x : FunctionField P)
    (harithmetic : ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a = x)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a = x := by sorry

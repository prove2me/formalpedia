-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_not_X_dvd_denom_of_building_integral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_X_dvd_denom_of_building_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:39.835109+00:00
-- url     : https://prove2.me/theorems/1a78fce3-b32c-4965-945a-86b9ec8cb20b
-- title:
--   Cartwright Steger: not X dvd denom of building integral
-- statement:
--   The Cartwright Steger construction uses the not X dvd denom of building integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L121-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L121-L167

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_X_dvd_denom_of_building_integral
    (P : BasePrime) (x : FunctionField P)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ¬ Polynomial.X ∣ x.denom := by sorry

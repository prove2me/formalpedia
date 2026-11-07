-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:39:26.182318+00:00
-- url     : https://prove2.me/theorems/d465a3d6-c66c-4076-9018-e76d3a3d3561
-- title:
--   Cartwright Steger: integral Arithmetic To Building Integer Ring algebra Map
-- statement:
--   The Cartwright Steger construction uses the integral Arithmetic To Building Integer Ring algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L51-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L51-L56

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
    (P : BasePrime) (f : PolynomialRing P) :
    integralArithmeticToBuildingIntegerRing P
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      Polynomial.coeToPowerSeries.ringHom f := by sorry

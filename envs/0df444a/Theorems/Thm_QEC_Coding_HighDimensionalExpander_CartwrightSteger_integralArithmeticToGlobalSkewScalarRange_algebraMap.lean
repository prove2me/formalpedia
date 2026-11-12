-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:57:24.777528+00:00
-- url     : https://prove2.me/theorems/b75e41fc-90e0-4ddc-b87e-d8da1c514818
-- title:
--   Cartwright Steger: integral Arithmetic To Global Skew Scalar Range algebra Map
-- statement:
--   The Cartwright Steger construction uses the integral Arithmetic To Global Skew Scalar Range algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L245-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L245-L250

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    integralArithmeticToGlobalSkewScalarRange P r
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      polynomialToGlobalSkewScalarRange P r f := by sorry

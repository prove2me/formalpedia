-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:33.567375+00:00
-- url     : https://prove2.me/theorems/53b639d3-a758-411b-af04-077e532e947e
-- title:
--   Cartwright Steger: arithmetic Finite Adele Supported At Place mem integral iff
-- statement:
--   One-place scalar support is integral at all arithmetic finite places
--   exactly when its nonzero coordinate is integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L63-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L63-L88

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleSupportedAtPlace P v x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ v.adicCompletionIntegers (FunctionField P) := by sorry

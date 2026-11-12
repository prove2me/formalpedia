-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleAt_supportedAtPlace_of_ne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAt_supportedAtPlace_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:01.26572+00:00
-- url     : https://prove2.me/theorems/9eaebfb5-44a5-4219-80da-75d553feabfe
-- title:
--   Cartwright Steger: arithmetic Finite Adele At supported At Place of ne
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele At supported At Place of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L50-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L50-L59

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAt_supportedAtPlace_of_ne
    (P : BasePrime)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hvw : w ≠ v)
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleAt P w
        (arithmeticFiniteAdeleSupportedAtPlace P v x) = 0 := by sorry

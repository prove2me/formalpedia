-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported_of_ne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:31.410193+00:00
-- url     : https://prove2.me/theorems/140212f7-1bf2-4dbc-811f-82a74804ea3c
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Algebra At Place supported of ne
-- statement:
--   A cyclic element supported at `v` projects to zero at every distinct
--   arithmetic finite place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L469-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L469-L483

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) = 0 := by sorry

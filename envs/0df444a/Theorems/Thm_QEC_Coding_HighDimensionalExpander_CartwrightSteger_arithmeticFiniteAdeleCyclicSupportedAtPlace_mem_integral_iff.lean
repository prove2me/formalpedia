-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:20.942433+00:00
-- url     : https://prove2.me/theorems/e11dbb79-edb9-4ae2-8021-e1951787ff9b
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Supported At Place mem integral iff
-- statement:
--   One-place cyclic support is globally integral exactly when every local
--   cyclic coordinate is adic integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L357-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L357-L367

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ ArithmeticAdicCyclicIntegralLattice P r v := by sorry

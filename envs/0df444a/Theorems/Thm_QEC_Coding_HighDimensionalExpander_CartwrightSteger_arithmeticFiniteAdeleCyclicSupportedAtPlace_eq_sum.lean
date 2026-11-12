-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicSupportedAtPlace_eq_sum
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicSupportedAtPlace_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:23:37.323647+00:00
-- url     : https://prove2.me/theorems/16094377-1ea5-4c99-bdac-b60881f6f93e
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Supported At Place eq sum
-- statement:
--   One-place cyclic support is the sum of the supported scalar cyclic
--   coordinates in the common construction-owned basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L281-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L281-L301

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicSupportedAtPlace_eq_sum
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x =
      ∑ p, TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtPlace P v
          ((arithmeticAdicCyclicBasis P r v).equivFun x p))
        (functionFieldCyclicBasis P r p) := by sorry

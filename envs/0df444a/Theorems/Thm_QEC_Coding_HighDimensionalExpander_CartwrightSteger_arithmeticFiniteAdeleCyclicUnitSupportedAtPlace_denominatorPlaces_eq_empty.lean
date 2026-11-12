-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_denominatorPlaces_eq_empty
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_denominatorPlaces_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:26:17.705719+00:00
-- url     : https://prove2.me/theorems/7bb9a504-86db-446d-ac34-9c5790925da2
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit Supported At Place denominator Places eq empty
-- statement:
--   A one-place patched local unit has empty global denominator support
--   when both the local unit and its inverse have integral cyclic coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L657-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L657-L685

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_denominatorPlaces_eq_empty
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ)
    (hu : (u : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v)
    (huInv : ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
        ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = ∅ := by sorry

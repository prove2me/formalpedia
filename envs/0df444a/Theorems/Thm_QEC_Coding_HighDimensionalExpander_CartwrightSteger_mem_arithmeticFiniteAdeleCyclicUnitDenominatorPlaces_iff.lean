-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:24.523614+00:00
-- url     : https://prove2.me/theorems/f4574f2a-02cb-4fa1-89e3-ebaff0466f97
-- title:
--   Cartwright Steger: mem arithmetic Finite Adele Cyclic Unit Denominator Places iff
-- statement:
--   Denominator membership can be read entirely from the projected local
--   unit and its inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L722-L737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L722-L737

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u ↔
      (arithmeticFiniteAdeleCyclicUnitAtPlace P r v u :
          ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v ∨
        (((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹ :
          (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
            ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v := by sorry

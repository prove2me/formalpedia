-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitAtPlace_clearAll_of_not_mem
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clearAll_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:27:24.772314+00:00
-- url     : https://prove2.me/theorems/be970955-63c2-4413-9184-dd5028e1ed10
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit At Place clear All of not mem
-- statement:
--   Complete denominator clearing preserves every coordinate that was not
--   in the original denominator support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L895-L905
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L895-L905

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clearAll_of_not_mem
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hw : w ∉ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r
          (arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList P r u) u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by sorry

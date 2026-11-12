-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlaceList
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlaceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:25:39.542318+00:00
-- url     : https://prove2.me/theorems/30da0b33-2e52-498a-9010-e93a51f57398
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit Denominator Places clear At Place List
-- statement:
--   Clearing a list removes exactly the set of places occurring in that
--   list from the denominator support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L820-L836
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L820-L836

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlaceList
    (P : BasePrime) (r : Rank)
    (places : List
      (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places u) =
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u \
        (places.toFinset : Set
          (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))) := by sorry

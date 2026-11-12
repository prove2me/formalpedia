-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitAtPlace_clearAtPlaceList_of_not_mem
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clearAtPlaceList_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:25:24.621594+00:00
-- url     : https://prove2.me/theorems/ffd19eed-38ba-4576-8141-9e2f7a311f94
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit At Place clear At Place List of not mem
-- statement:
--   Clearing places not containing `w` preserves the `w`-projection
--   exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L840-L862
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L840-L862

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clearAtPlaceList_of_not_mem
    (P : BasePrime) (r : Rank)
    (places : List
      (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)))
    (w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hw : w ∉ places)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by sorry

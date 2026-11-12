-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlace
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:25:13.320907+00:00
-- url     : https://prove2.me/theorems/35e4a38e-de37-40cd-a653-2a345db44b48
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit Denominator Places clear At Place
-- statement:
--   Exact support effect of one-place correction: it deletes precisely the
--   chosen place and changes no other denominator membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L786-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L786-L802

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) =
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u \ {v} := by sorry

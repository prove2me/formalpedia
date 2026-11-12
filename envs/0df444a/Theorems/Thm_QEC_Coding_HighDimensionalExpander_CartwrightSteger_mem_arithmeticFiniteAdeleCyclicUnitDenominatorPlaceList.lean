-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:13.005324+00:00
-- url     : https://prove2.me/theorems/ee159205-2cac-44e1-9853-221215e620de
-- title:
--   Cartwright Steger: mem arithmetic Finite Adele Cyclic Unit Denominator Place List
-- statement:
--   The Cartwright Steger construction uses the mem arithmetic Finite Adele Cyclic Unit Denominator Place List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L872-L878
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L872-L878

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList P r u ↔
      v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u := by sorry

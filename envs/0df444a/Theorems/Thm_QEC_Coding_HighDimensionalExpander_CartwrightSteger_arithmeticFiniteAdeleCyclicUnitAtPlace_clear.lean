-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitAtPlace_clear
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:21:35.337077+00:00
-- url     : https://prove2.me/theorems/8f9b21f8-f21b-416f-bb93-900075587af9
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit At Place clear
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele Cyclic Unit At Place clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L750-L764
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L750-L764

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clear
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r v
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) = 1 := by sorry

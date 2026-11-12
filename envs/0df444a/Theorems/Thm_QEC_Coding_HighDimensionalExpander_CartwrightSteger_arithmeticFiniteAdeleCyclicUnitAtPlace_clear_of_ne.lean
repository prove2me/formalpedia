-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:21:59.648273+00:00
-- url     : https://prove2.me/theorems/3b82230f-50fe-4c53-9904-0ed077d0c8e1
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit At Place clear of ne
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele Cyclic Unit At Place clear of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L766-L782
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L766-L782

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by sorry

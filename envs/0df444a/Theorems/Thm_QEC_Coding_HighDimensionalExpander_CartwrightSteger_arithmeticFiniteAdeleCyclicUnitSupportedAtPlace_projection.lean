-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:43.405802+00:00
-- url     : https://prove2.me/theorems/90a3da5c-384f-485c-971f-3460a7d3ab4b
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit Supported At Place projection
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele Cyclic Unit Supported At Place projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L687-L695
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L687-L695

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = u := by sorry

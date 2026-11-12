-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:23.483532+00:00
-- url     : https://prove2.me/theorems/5064418f-a82a-4ea3-b3d5-630de153b612
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit Supported At Place projection of ne
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele Cyclic Unit Supported At Place projection of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L697-L706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L697-L706

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = 1 := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch_of_ne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:43.560867+00:00
-- url     : https://prove2.me/theorems/021d3453-3994-4dbd-bc08-29d5570cc1b4
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Algebra At Place patch of ne
-- statement:
--   The Cartwright Steger construction uses the arithmetic Finite Adele Cyclic Algebra At Place patch of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L611-L621
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L611-L621

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w
        (arithmeticFiniteAdeleCyclicPatchAtPlace P r v x) = 1 := by sorry

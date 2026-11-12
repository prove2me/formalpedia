-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtPlace
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtPlace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:23:16.783105+00:00
-- url     : https://prove2.me/theorems/94428909-4737-4b1f-87f4-cec9a67c3d17
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Basis equiv Fun supported At Place
-- statement:
--   Cyclic coordinates commute with support at an arbitrary arithmetic
--   finite place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L318-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L318-L353

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) p =
      arithmeticFiniteAdeleSupportedAtPlace P v
        ((arithmeticAdicCyclicBasis P r v).equivFun x p) := by sorry

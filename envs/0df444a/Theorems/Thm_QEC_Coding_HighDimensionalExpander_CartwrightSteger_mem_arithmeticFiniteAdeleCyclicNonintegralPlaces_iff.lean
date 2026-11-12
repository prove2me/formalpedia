-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:11.933609+00:00
-- url     : https://prove2.me/theorems/af87c4d1-b7e7-418d-8b3a-f7ffa0ea5093
-- title:
--   Cartwright Steger: mem arithmetic Finite Adele Cyclic Nonintegral Places iff
-- statement:
--   A place belongs to the nonintegral support of an adelic cyclic element
--   exactly when its projected local cyclic element is outside the local
--   integral lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L439-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L439-L465

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    v ∈ arithmeticFiniteAdeleCyclicNonintegralPlaces P r x ↔
      arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x ∉
        ArithmeticAdicCyclicIntegralLattice P r v := by sorry

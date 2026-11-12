-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_mem_arithmeticAdicCyclicIntegralLattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_mem_arithmeticAdicCyclicIntegralLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:25.061963+00:00
-- url     : https://prove2.me/theorems/7c7ce4b0-e2f0-443b-94e4-ae13cad60414
-- title:
--   Cartwright Steger: one mem arithmetic Adic Cyclic Integral Lattice
-- statement:
--   The Cartwright Steger construction uses the one mem arithmetic Adic Cyclic Integral Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L271-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L271-L277

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_mem_arithmeticAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    (1 : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by sorry

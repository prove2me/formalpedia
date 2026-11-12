-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclic_diagonal_mem_integralLattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclic_diagonal_mem_integralLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:25.205915+00:00
-- url     : https://prove2.me/theorems/d42a8bb5-097c-4197-b862-2e501791b959
-- title:
--   Cartwright Steger: arithmetic Adic Cyclic diagonal mem integral Lattice
-- statement:
--   Every element of the actual arithmetic cyclic order is integral at
--   every arithmetic finite place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L258-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L258-L269

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclic_diagonal_mem_integralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    TensorProduct.tmul (FunctionField P) 1 x ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by sorry

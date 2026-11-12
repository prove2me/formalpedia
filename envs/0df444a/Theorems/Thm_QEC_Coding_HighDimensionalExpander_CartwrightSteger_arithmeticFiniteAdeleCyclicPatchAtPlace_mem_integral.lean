-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:24:38.448661+00:00
-- url     : https://prove2.me/theorems/5e8754b7-6c9b-4c6d-b2ec-ee4d334387fd
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Patch At Place mem integral
-- statement:
--   Patching an integral adic cyclic element at one place and the identity
--   elsewhere preserves the all-place finite-adelic integral lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L562-L578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L562-L578

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v)
    (hx : x ∈ ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicPatchAtPlace P r v x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclicBasis_equivFun_diagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclicBasis_equivFun_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:43.310661+00:00
-- url     : https://prove2.me/theorems/2f9b0b47-46ff-47fd-854c-95f2734824a3
-- title:
--   Cartwright Steger: arithmetic Adic Cyclic Basis equiv Fun diagonal
-- statement:
--   Cyclic coordinates commute with diagonal scalar extension to an
--   arbitrary arithmetic adic completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L242-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L242-L254

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticAdicCyclicBasis P r v).equivFun
        (TensorProduct.tmul (FunctionField P) 1 x) p =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P))
          ((functionFieldCyclicBasis P r).equivFun x p) := by sorry

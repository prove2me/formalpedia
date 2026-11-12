-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclicBasis_equivFun_atPlace
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclicBasis_equivFun_atPlace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:23:39.524234+00:00
-- url     : https://prove2.me/theorems/e9a22ebd-c1c7-4120-ac1d-46060f43c6a1
-- title:
--   Cartwright Steger: arithmetic Adic Cyclic Basis equiv Fun at Place
-- statement:
--   Construction-owned cyclic coordinates commute with projection from the
--   finite adeles to any arithmetic adic completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L382-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean#L382-L434

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclicBasis_equivFun_atPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticAdicCyclicBasis P r v).equivFun
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x) p =
      arithmeticFiniteAdeleAt P v
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) := by sorry

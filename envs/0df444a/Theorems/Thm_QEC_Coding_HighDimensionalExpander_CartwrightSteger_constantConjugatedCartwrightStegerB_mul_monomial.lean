-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_mul_monomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_mul_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:10.345412+00:00
-- url     : https://prove2.me/theorems/339bba10-a3f0-4e8b-a8d3-e869954ec351
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B mul monomial
-- statement:
--   Left multiplication by the conjugated generator on a cyclic monomial,
--   before inserting the proved finite-sum inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L541-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L541-L574

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_mul_monomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    (constantConjugatedCartwrightStegerB P r u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k) =
      constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        constantMatrix P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ k := by sorry

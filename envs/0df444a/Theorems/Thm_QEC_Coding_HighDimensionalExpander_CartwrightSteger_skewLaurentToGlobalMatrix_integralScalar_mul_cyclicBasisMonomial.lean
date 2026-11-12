-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:58:10.975557+00:00
-- url     : https://prove2.me/theorems/1a472036-348e-4a55-827a-18220b0760bb
-- title:
--   Cartwright Steger: skew Laurent To Global Matrix integral Scalar mul cyclic Basis Monomial
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Global Matrix integral Scalar mul cyclic Basis Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L305-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L305-L323

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P)
    (f : CartwrightStegerSkewLaurentRing P r)
    (hf : skewLaurentToGlobalMatrix P r f =
      functionFieldScalarMatrix P r
        (integralArithmeticToFunctionField P a))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentToGlobalMatrix P r
        (f * skewLaurentCyclicBasisMonomial P r p) =
      (integralArithmeticToFunctionField P a) •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by sorry

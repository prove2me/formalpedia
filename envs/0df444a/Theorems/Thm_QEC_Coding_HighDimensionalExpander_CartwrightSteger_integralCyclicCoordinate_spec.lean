-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralCyclicCoordinate_spec
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralCyclicCoordinate_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:11:22.861707+00:00
-- url     : https://prove2.me/theorems/deaf8fec-c8ff-43b0-82d4-0876060ef926
-- title:
--   Cartwright Steger: integral Cyclic Coordinate spec
-- statement:
--   The Cartwright Steger construction uses the integral Cyclic Coordinate spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstruction.lean#L21-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstruction.lean#L21-L31

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralCyclicCoordinate_spec
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    integralArithmeticToFunctionField P
        (integralCyclicCoordinate P r x hcoords p) =
      (functionFieldCyclicBasis P r).repr x p := by sorry

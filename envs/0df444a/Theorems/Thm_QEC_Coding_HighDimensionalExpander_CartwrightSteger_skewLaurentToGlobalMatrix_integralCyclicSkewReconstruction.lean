-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:15:28.984096+00:00
-- url     : https://prove2.me/theorems/f70b2c46-5305-46ae-9a52-74958a55e485
-- title:
--   Cartwright Steger: skew Laurent To Global Matrix integral Cyclic Skew Reconstruction
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Global Matrix integral Cyclic Skew Reconstruction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L19-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L19-L36

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    skewLaurentToGlobalMatrix P r
        (integralCyclicSkewReconstruction P r x hcoords) =
      ∑ p, (functionFieldCyclicBasis P r).repr x p •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralCyclicCoordinates
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralCyclicCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:14:46.948212+00:00
-- url     : https://prove2.me/theorems/40906841-0b14-4969-a722-c2dcc57b610d
-- title:
--   Cartwright Steger: exists skew Laurent of integral Cyclic Coordinates
-- statement:
--   The Cartwright Steger construction uses the exists skew Laurent of integral Cyclic Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L57-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L57-L67

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralCyclicCoordinates
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f = x.1 := by sorry

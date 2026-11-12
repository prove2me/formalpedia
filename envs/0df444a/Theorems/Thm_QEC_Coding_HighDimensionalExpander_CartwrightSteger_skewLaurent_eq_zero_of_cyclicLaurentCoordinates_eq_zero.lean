-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_eq_zero_of_cyclicLaurentCoordinates_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_eq_zero_of_cyclicLaurentCoordinates_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:19:48.901692+00:00
-- url     : https://prove2.me/theorems/d41e4fdb-aadd-4d0c-acef-be64bbe315b2
-- title:
--   Cartwright Steger: skew Laurent eq zero of cyclic Laurent Coordinates eq zero
-- statement:
--   The Cartwright Steger construction uses the skew Laurent eq zero of cyclic Laurent Coordinates eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L150-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L150-L166

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_eq_zero_of_cyclicLaurentCoordinates_eq_zero
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (hzero : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      skewLaurentCyclicLaurentCoordinate P r f p = 0) :
    f = 0 := by sorry

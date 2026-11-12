-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_add
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:20:51.45024+00:00
-- url     : https://prove2.me/theorems/1f60347d-9127-4b5b-8504-e500cfd41663
-- title:
--   Cartwright Steger: skew Laurent Cyclic Laurent Coordinate add
-- statement:
--   The Cartwright Steger construction uses the skew Laurent Cyclic Laurent Coordinate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L83-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L83-L97

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_add
    (P : BasePrime) (r : Rank)
    (f g : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentCyclicLaurentCoordinate P r (f + g) p =
      skewLaurentCyclicLaurentCoordinate P r f p +
        skewLaurentCyclicLaurentCoordinate P r g p := by sorry

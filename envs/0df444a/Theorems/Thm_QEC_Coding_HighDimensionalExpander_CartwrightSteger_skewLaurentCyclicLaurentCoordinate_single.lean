-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_single
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:19:53.716334+00:00
-- url     : https://prove2.me/theorems/9ecfae08-3093-4d26-95e1-b3d8931db020
-- title:
--   Cartwright Steger: skew Laurent Cyclic Laurent Coordinate single
-- statement:
--   The Cartwright Steger construction uses the skew Laurent Cyclic Laurent Coordinate single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L69-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L69-L81

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_single
    (P : BasePrime) (r : Rank)
    (m : Multiplicative ℤ) (c : ConstantExtension P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentCyclicLaurentCoordinate P r
        (SkewMonoidAlgebra.single m c) p =
      if skewExponentResidue r m.toAdd = p.2 then
        LaurentPolynomial.C ((constantBasis P r).repr c p.1) *
          LaurentPolynomial.T (skewExponentQuotient r m.toAdd)
      else 0 := by sorry

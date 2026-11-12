-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_apply_quotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_apply_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:19:45.227757+00:00
-- url     : https://prove2.me/theorems/407650c5-aa9f-4c70-a7e0-86c850527de4
-- title:
--   Cartwright Steger: skew Laurent Cyclic Laurent Coordinate apply quotient
-- statement:
--   The Cartwright Steger construction uses the skew Laurent Cyclic Laurent Coordinate apply quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L99-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L99-L148

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_apply_quotient
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (i : Fin r.matrixRank) (n : ℤ) :
    (skewLaurentCyclicLaurentCoordinate P r f
        (i, skewExponentResidue r n)).coeff (skewExponentQuotient r n) =
      (constantBasis P r).repr
        (f.coeff (Multiplicative.ofAdd n)) i := by sorry

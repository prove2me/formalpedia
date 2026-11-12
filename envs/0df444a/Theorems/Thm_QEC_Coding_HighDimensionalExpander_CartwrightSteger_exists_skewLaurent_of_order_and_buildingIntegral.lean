-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_order_and_buildingIntegral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_order_and_buildingIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:15:37.859915+00:00
-- url     : https://prove2.me/theorems/62b2bf78-f17f-46a1-9a03-cf3f1517579f
-- title:
--   Cartwright Steger: exists skew Laurent of order and building Integral
-- statement:
--   The Cartwright Steger construction uses the exists skew Laurent of order and building Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L69-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L69-L88

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_order_and_buildingIntegral
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x)) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        (cartwrightStegerOrderToCyclicAlgebra P r x).1 := by sorry

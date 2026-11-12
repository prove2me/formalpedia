-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_orderYUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_orderYUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:46:47.096926+00:00
-- url     : https://prove2.me/theorems/d3d4d3d5-ca96-4ba1-9ff8-7359f2d103ed
-- title:
--   Cartwright Steger: order Unit To Global GL order YUnit
-- statement:
--   The Cartwright Steger construction uses the order Unit To Global GL order YUnit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L84-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L84-L90

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_orderYUnit
    (P : BasePrime) (r : Rank) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderYUnit P r) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (Units.mk0 (splittingY P r) (splittingY_ne_zero P r)) := by sorry

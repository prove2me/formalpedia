-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalPGL_normalizedOrderUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalPGL_normalizedOrderUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:46:44.503115+00:00
-- url     : https://prove2.me/theorems/c669df55-c78b-4d04-a25c-3aa4da0024a0
-- title:
--   Cartwright Steger: order Unit To Global PGL normalized Order Unit
-- statement:
--   The central normalization used to choose an integral building
--   representative is invisible in the global projective representation too.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L94-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L94-L107

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalPGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    orderUnitToGlobalPGL P r (normalizedOrderUnit P r u q) =
      orderUnitToGlobalPGL P r u := by sorry

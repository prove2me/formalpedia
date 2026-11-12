-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_normalizedOrderUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_normalizedOrderUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:43:16.962015+00:00
-- url     : https://prove2.me/theorems/7975959a-9b18-4374-bdab-dbf758b2682b
-- title:
--   Cartwright Steger: order Unit To Building PGL normalized Order Unit
-- statement:
--   The Cartwright Steger construction uses the order Unit To Building PGL normalized Order Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L112-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L112-L125

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    orderUnitToBuildingPGL P r (normalizedOrderUnit P r u q) =
      orderUnitToBuildingPGL P r u := by sorry

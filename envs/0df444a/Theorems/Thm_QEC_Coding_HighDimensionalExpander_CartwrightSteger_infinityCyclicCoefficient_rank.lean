-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:56.962372+00:00
-- url     : https://prove2.me/theorems/d3e57751-d644-45c2-b1b6-ca09c3f0ea40
-- title:
--   Cartwright Steger: infinity Cyclic Coefficient rank
-- statement:
--   The Cartwright Steger construction uses the infinity Cyclic Coefficient rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L257-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L257-L260

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    infinityCyclicCoefficient P r u r.matrixRank = 1 := by sorry

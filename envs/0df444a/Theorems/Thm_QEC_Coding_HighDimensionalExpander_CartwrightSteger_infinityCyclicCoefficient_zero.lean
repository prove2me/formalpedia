-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:55.999539+00:00
-- url     : https://prove2.me/theorems/9baa178d-2c3c-419e-884b-866943f3d592
-- title:
--   Cartwright Steger: infinity Cyclic Coefficient zero
-- statement:
--   The Cartwright Steger construction uses the infinity Cyclic Coefficient zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L250-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L250-L254

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    infinityCyclicCoefficient P r u 0 = 1 := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_conj_constantUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_conj_constantUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:56.626772+00:00
-- url     : https://prove2.me/theorems/51843af9-be6d-45be-834b-2920ea668ffc
-- title:
--   Cartwright Steger: cyclic Generator conj constant Unit
-- statement:
--   Conjugation by the global cyclic generator realizes arithmetic
--   Frobenius on constant units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L37-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L37-L48

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_conj_constantUnit
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    cyclicGenerator P r * constantUnitMatrix P r u *
        (cyclicGenerator P r)⁻¹ =
      constantUnitMatrix P r (constantFrobeniusUnitEquiv P r u) := by sorry

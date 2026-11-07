-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_conj_constantUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_conj_constantUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:54.177091+00:00
-- url     : https://prove2.me/theorems/0669ac2e-8177-4172-90bf-50a6cdd69450
-- title:
--   Cartwright Steger: cyclic Generator pow conj constant Unit
-- statement:
--   Natural powers of the global cyclic generator realize the
--   corresponding powers of Frobenius.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L52-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L52-L82

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_conj_constantUnit
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    cyclicGenerator P r ^ j * constantUnitMatrix P r u *
        (cyclicGenerator P r ^ j)⁻¹ =
      constantUnitMatrix P r
        ((constantFrobeniusUnitEquiv P r ^ j) u) := by sorry

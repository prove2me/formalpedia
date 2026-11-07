-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:10.697002+00:00
-- url     : https://prove2.me/theorems/3dcc6737-6f81-4e11-b88b-267f0db4543a
-- title:
--   Cartwright Steger: infinity Cyclic Coefficient coe
-- statement:
--   Coercing the cyclic coefficient gives the corresponding quotient in
--   the constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L224-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L224-L230

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_coe
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    (infinityCyclicCoefficient P r u k : ConstantExtension P r) =
      (u : ConstantExtension P r) *
        ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹ := by sorry

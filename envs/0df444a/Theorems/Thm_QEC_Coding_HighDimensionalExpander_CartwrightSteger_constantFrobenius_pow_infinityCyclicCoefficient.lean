-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_infinityCyclicCoefficient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_infinityCyclicCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:57.278122+00:00
-- url     : https://prove2.me/theorems/14d8d1be-6d47-413c-86b4-40725ec5778b
-- title:
--   Cartwright Steger: constant Frobenius pow infinity Cyclic Coefficient
-- statement:
--   Frobenius shifts both indices in a cyclic coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L263-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L263-L280

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_infinityCyclicCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) =
      (constantFrobenius P r ^ k) (u : ConstantExtension P r) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by sorry

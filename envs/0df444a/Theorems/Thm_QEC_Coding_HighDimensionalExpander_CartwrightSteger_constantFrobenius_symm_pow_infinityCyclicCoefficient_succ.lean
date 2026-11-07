-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:41.52701+00:00
-- url     : https://prove2.me/theorems/77aa0ddd-6527-499d-8632-4dd9fc6c671f
-- title:
--   Cartwright Steger: constant Frobenius symm pow infinity Cyclic Coefficient succ
-- statement:
--   The shifted predecessor coefficient has the same terminal denominator
--   as the leading coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L301-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L301-L315

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u (i + 1) :
            ConstantExtension P r)) =
      (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r)) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by sorry

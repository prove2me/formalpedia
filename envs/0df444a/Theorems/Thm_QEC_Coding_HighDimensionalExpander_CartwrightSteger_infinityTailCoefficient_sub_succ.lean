-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityTailCoefficient_sub_succ
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityTailCoefficient_sub_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:53.867021+00:00
-- url     : https://prove2.me/theorems/a6e11816-29ca-478d-a961-10c10f489a68
-- title:
--   Cartwright Steger: infinity Tail Coefficient sub succ
-- statement:
--   Consecutive tail coefficients differ by the exact equation-(9)
--   coefficient.  The resulting cyclic coefficient is indexed by the actual
--   exponent `k + i`, before reduction modulo the cyclic degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L473-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L473-L492

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityTailCoefficient_sub_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    ζ * (constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r) -
        (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          (constantFrobenius P r).symm
            ((constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u (i + 1) :
                ConstantExtension P r)) =
      infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r) := by sorry

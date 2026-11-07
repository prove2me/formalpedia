-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnit_conj_cyclicGenerator_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnit_conj_cyclicGenerator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:50.057973+00:00
-- url     : https://prove2.me/theorems/90440418-8905-46fc-97e7-02e24bf9b31e
-- title:
--   Cartwright Steger: constant Unit conj cyclic Generator pow
-- statement:
--   Constant conjugation of `z^k` produces exactly the source coefficient
--   `u / phi^k(u)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L405-L442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L405-L442

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnit_conj_cyclicGenerator_pow
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    constantUnitMatrix P r u * cyclicGenerator P r ^ k *
        (constantUnitMatrix P r u)⁻¹ =
      constantUnitMatrix P r (infinityCyclicCoefficient P r u k) *
        cyclicGenerator P r ^ k := by sorry

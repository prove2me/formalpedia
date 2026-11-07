-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCoefficient_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:20:35.169526+00:00
-- url     : https://prove2.me/theorems/760ca918-6c0e-42e2-b0b1-85c382a33a04
-- title:
--   Cartwright Steger: infinity Conjugation Coefficient zero
-- statement:
--   At `k = 0`, the source coefficient reduces to
--   `ζ - phi⁻¹(ζ)`, independently of `u`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L334-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L334-L340

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCoefficient_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (ζ : ConstantExtension P r) :
    infinityConjugationCoefficient P r u 0 ζ =
      ζ - (constantFrobenius P r ^ (-1 : ℤ)) ζ := by sorry

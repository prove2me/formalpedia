-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_z_mul_constant
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_z_mul_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:53.827882+00:00
-- url     : https://prove2.me/theorems/9060c834-8f7e-4094-b683-7b1cf0a6116c
-- title:
--   Cartwright Steger: skew Laurent z mul constant
-- statement:
--   The defining skew relation `z c = Frobenius(c) z`, proved from the
--   constructed multiplication and action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L96-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L96-L104

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_z_mul_constant
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 *
        SkewMonoidAlgebra.single 1 c =
      SkewMonoidAlgebra.single 1 (constantFrobenius P r c) *
        SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 := by sorry

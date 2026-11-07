-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_action_eq_frobenius
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_action_eq_frobenius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:44.465395+00:00
-- url     : https://prove2.me/theorems/24dd508a-3090-4d16-aed9-b24cbea6381b
-- title:
--   Cartwright Steger: one action eq frobenius
-- statement:
--   The degree-one action is exactly arithmetic Frobenius.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L58-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L58-L64

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_action_eq_frobenius
    (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    Multiplicative.ofAdd (1 : ℤ) • c = constantFrobenius P r c := by sorry

-- Prove2me | Theorems.Thm_QuadraticFloor_zmod5_eq_pow_lg
-- name    : QuadraticFloor.zmod5_eq_pow_lg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:35.785802+00:00
-- url     : https://prove2.me/theorems/28cabf38-caec-475d-9c38-48ecabcd04e3
-- title:
--   Quadratic Floor: zmod5 eq pow lg
-- statement:
--   The Quadratic Floor construction uses the zmod5 eq pow lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L24-L24
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L24-L24

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.zmod5_eq_pow_lg (a : ZMod 5) (ha : a ≠ 0) : a = 2 ^ lg5 a := by sorry

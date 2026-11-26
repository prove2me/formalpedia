-- Prove2me | Theorems.Thm_QuadraticFloor_xixi_two
-- name    : QuadraticFloor.xixi_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:21.660096+00:00
-- url     : https://prove2.me/theorems/67a99054-2bae-5fcc-9275-9c08b74e5bac
-- title:
--   Quadratic Floor: xixi two
-- statement:
--   The Quadratic Floor construction uses the xixi two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L67-L68
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L67-L68

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.xixi_two : (xi * xi) 2 = -1 := by sorry

-- Prove2me | Theorems.Thm_QuadraticFloor_char5_ext
-- name    : QuadraticFloor.char5_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:23.321173+00:00
-- url     : https://prove2.me/theorems/0d8cb6c9-3450-4643-8f7f-008e0f131c11
-- title:
--   Quadratic Floor: char5 ext
-- statement:
--   A character modulo `5` is determined by its value at `2`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L43-L47
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L43-L47

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.char5_ext {ψ ψ' : DirichletCharacter ℂ 5} (h : ψ 2 = ψ' 2) : ψ = ψ' := by sorry

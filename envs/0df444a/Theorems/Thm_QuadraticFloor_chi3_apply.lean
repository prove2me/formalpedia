-- Prove2me | Theorems.Thm_QuadraticFloor_chi3_apply
-- name    : QuadraticFloor.chi3_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:32.665995+00:00
-- url     : https://prove2.me/theorems/12b8e977-a3c3-439f-8644-ce110becebfb
-- title:
--   Quadratic Floor: chi3 apply
-- statement:
--   The Quadratic Floor construction uses the chi3 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L128-L129
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L128-L129

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.chi3_apply (x : ℕ) : chi3 (x : ZMod 3) = (legendreSym 3 x : ℂ) := by sorry

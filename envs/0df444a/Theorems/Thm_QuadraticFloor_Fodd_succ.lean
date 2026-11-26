-- Prove2me | Theorems.Thm_QuadraticFloor_Fodd_succ
-- name    : QuadraticFloor.Fodd_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:48.427677+00:00
-- url     : https://prove2.me/theorems/6c4682a8-deba-52ff-b6fb-79bdca6b7089
-- title:
--   Quadratic Floor: Fodd succ
-- statement:
--   The Quadratic Floor construction uses the Fodd succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L161-L200
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L161-L200

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.Fodd_succ (hp2 : p ≠ 2) (c : ℤ) :
    Fodd p (c + 1) = Fodd p c + (-2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3))) := by sorry

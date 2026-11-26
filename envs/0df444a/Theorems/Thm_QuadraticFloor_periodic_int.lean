-- Prove2me | Theorems.Thm_QuadraticFloor_periodic_int
-- name    : QuadraticFloor.periodic_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:21.540237+00:00
-- url     : https://prove2.me/theorems/5582cac0-1168-5857-a61f-572d3bcecbd4
-- title:
--   Quadratic Floor: periodic int
-- statement:
--   The Quadratic Floor construction uses the periodic int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L110-L115
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L110-L115

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.periodic_int {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (m k : ℤ) : g (m + p * k) = g m := by sorry

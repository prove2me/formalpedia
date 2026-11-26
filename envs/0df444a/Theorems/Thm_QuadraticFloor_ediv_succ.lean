-- Prove2me | Theorems.Thm_QuadraticFloor_ediv_succ
-- name    : QuadraticFloor.ediv_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:48.289352+00:00
-- url     : https://prove2.me/theorems/fc38bd15-7bf6-4654-84fe-eee7b6a9569b
-- title:
--   Quadratic Floor: ediv succ
-- statement:
--   The Quadratic Floor construction uses the ediv succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L140-L159
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L140-L159

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

theorem QuadraticFloor.ediv_succ (hp0 : 0 < (p : ℤ)) (v : ℤ) :
    (v + 1) / (p : ℤ) = v / p + if (p : ℤ) ∣ v + 1 then 1 else 0 := by sorry

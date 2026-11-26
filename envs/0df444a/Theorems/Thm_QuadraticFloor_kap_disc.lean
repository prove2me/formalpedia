-- Prove2me | Theorems.Thm_QuadraticFloor_kap_disc
-- name    : QuadraticFloor.kap_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:54.484629+00:00
-- url     : https://prove2.me/theorems/437570f7-20da-442b-9dc5-3c61c45c0c3e
-- title:
--   Quadratic Floor: kap disc
-- statement:
--   `κ_p(D) = (-1)^C` for the discriminant of an admissible pair.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L155-L167
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L155-L167

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.kap_disc {d : ℕ} {C : ℤ} (hd : d % 8 = if Even C then 1 else 5) :
    kap p (d : ZMod 8) = (C.negOnePow : ℤ) := by sorry

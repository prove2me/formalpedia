-- Prove2me | Theorems.Thm_QuadraticFloor_quartic_mod_four
-- name    : QuadraticFloor.quartic_mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:55.734397+00:00
-- url     : https://prove2.me/theorems/5d2712e1-bab4-5ee1-b288-846a68befaff
-- title:
--   Quadratic Floor: quartic mod four
-- statement:
--   **Proposition 4.6.** `Re B_{1,Θ_p}` is an integer congruent to `2 (z_1 - z_3)` modulo `4`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L123-L125
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L123-L125

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.quartic_mod_four (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] := by sorry

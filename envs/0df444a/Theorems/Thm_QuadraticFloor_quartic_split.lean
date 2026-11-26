-- Prove2me | Theorems.Thm_QuadraticFloor_quartic_split
-- name    : QuadraticFloor.quartic_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:26.494707+00:00
-- url     : https://prove2.me/theorems/3d02ba26-aa0b-52dc-9307-986b80169f93
-- title:
--   Quadratic Floor: quartic split
-- statement:
--   **Corollary 4.5 (the quartic split).** `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L118-L120
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L118-L120

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.quartic_split (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re := by sorry

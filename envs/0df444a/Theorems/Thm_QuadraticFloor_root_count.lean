-- Prove2me | Theorems.Thm_QuadraticFloor_root_count
-- name    : QuadraticFloor.root_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:15.057488+00:00
-- url     : https://prove2.me/theorems/16ca65cf-cce4-4c48-99b4-14cb5d3a5cd0
-- title:
--   Quadratic Floor: root count
-- statement:
--   **Lemma 2.1 (root count).** If `A + B` is even and `p ∤ A`, then
--   `𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((B² - 4AC + 8Aj)/p))`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L26-L29
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L26-L29

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.root_count (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) := by sorry

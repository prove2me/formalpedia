-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_root_count__8bce20a9a3c2
-- name    : P2M_QuadraticFloor_root_count__8bce20a9a3c2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:50.830568+00:00
-- url     : https://prove2.me/theorems/4ee42f68-4cbf-404d-accf-f05ff37812b8
-- title:
--   P2 M Quadratic Floor root count  8bce20a9a3c2: P2 M Quadratic Floor root count  8bce20a9a3c2
-- statement:
--   **Lemma 2.1 (root count).** If `A + B` is even and `p ∤ A`, then
--   `𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((B² - 4AC + 8Aj)/p))`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L132-L186
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L132-L186

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_root_count__8bce20a9a3c2 (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) := by sorry

alias «QuadraticFloor».«root_count'» := P2M_QuadraticFloor_root_count__8bce20a9a3c2

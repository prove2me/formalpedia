-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_monic_odd__8e05b6979b8c
-- name    : P2M_QuadraticFloor_monic_odd__8e05b6979b8c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:48.902885+00:00
-- url     : https://prove2.me/theorems/ebdc2b1b-e79b-5ecb-bb30-014a63986550
-- title:
--   P2 M Quadratic Floor monic odd  8e05b6979b8c: P2 M Quadratic Floor monic odd  8e05b6979b8c
-- statement:
--   **Theorem 7.1(1), odd shifts.** For `a = 2t + 1` and `b' = b - t(t+1)`,
--   `𝒮_{a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L204-L239
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L204-L239

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_monic_odd__8e05b6979b8c (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by sorry

alias «QuadraticFloor».«monic_odd'» := P2M_QuadraticFloor_monic_odd__8e05b6979b8c

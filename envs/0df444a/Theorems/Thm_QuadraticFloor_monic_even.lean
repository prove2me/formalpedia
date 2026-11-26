-- Prove2me | Theorems.Thm_QuadraticFloor_monic_even
-- name    : QuadraticFloor.monic_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:55.207935+00:00
-- url     : https://prove2.me/theorems/fe16ec58-e354-517a-a46b-fb79345a4dac
-- title:
--   Quadratic Floor: monic even
-- statement:
--   **Theorem 7.1(2).** For `a = 2t` and `b' = b - t²`,
--   `𝒮_{1,a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L138-L141
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L138-L141

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.monic_even (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) := by sorry

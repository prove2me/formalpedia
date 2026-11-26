-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_monic_even__b68b70dddb0d
-- name    : P2M_QuadraticFloor_monic_even__b68b70dddb0d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:00.179176+00:00
-- url     : https://prove2.me/theorems/876cdc23-b8ae-5b07-9608-1a00fc26792e
-- title:
--   P2 M Quadratic Floor monic even  b68b70dddb0d: P2 M Quadratic Floor monic even  b68b70dddb0d
-- statement:
--   **Theorem 7.1(2), even shifts.** For `a = 2t` and `b' = b - t²`,
--   `𝒮_{a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L250-L310
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L250-L310

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_monic_even__b68b70dddb0d (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) := by sorry

alias «QuadraticFloor».«monic_even'» := P2M_QuadraticFloor_monic_even__b68b70dddb0d

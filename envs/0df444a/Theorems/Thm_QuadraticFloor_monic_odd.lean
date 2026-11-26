-- Prove2me | Theorems.Thm_QuadraticFloor_monic_odd
-- name    : QuadraticFloor.monic_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:04:06.866948+00:00
-- url     : https://prove2.me/theorems/27caa731-4f44-4f58-927e-f095eba4148f
-- title:
--   Quadratic Floor: monic odd
-- statement:
--   **Theorem 7.1(1).** For `a = 2t + 1` and `b' = b - t(t+1)`,
--   `𝒮_{1,a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L131-L134
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L131-L134

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.monic_odd (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by sorry

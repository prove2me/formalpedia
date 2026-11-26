-- Prove2me | Theorems.Thm_QuadraticFloor_sum_modEq_card
-- name    : QuadraticFloor.sum_modEq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:49.897929+00:00
-- url     : https://prove2.me/theorems/2a9ba946-97f9-5e9d-81da-7325eaf8740b
-- title:
--   Quadratic Floor: sum mod Eq card
-- statement:
--   A sum of values in `{-1, 0, 1}` has the parity of the number of nonzero terms.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L244-L250
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L244-L250

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

theorem QuadraticFloor.sum_modEq_card {s : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1) :
    ∑ j ∈ s, f j ≡ (s.filter fun j => f j ≠ 0).card [ZMOD 2] := by sorry

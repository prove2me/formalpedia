-- Prove2me | Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
-- name    : QuadraticFloor.eta_mul_chi4_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:57.536938+00:00
-- url     : https://prove2.me/theorems/c7b1371a-fb74-451e-856a-d87278757579
-- title:
--   Quadratic Floor: eta mul chi4 sq
-- statement:
--   The Quadratic Floor construction uses the eta mul chi4 sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L295-L301
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L295-L301

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}

theorem QuadraticFloor.eta_mul_chi4_sq (p x : ℕ) : (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2 = eta p x := by sorry

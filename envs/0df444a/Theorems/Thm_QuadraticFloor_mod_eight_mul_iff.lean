-- Prove2me | Theorems.Thm_QuadraticFloor_mod_eight_mul_iff
-- name    : QuadraticFloor.mod_eight_mul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:27.488149+00:00
-- url     : https://prove2.me/theorems/7370585c-bab0-44f3-9a66-6d77d226e873
-- title:
--   Quadratic Floor: mod eight mul iff
-- statement:
--   The Quadratic Floor construction uses the mod eight mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L107-L114
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L107-L114

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.mod_eight_mul_iff {A x d : ℕ} (hA : Odd A) (hd : d < 8 * A) :
    x % (8 * A) = d ↔ x % 8 = d % 8 ∧ x % A = d % A := by sorry

-- Prove2me | Theorems.Thm_QuadraticFloor_isUnit_intCast_of_gcd
-- name    : QuadraticFloor.isUnit_intCast_of_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:46.298447+00:00
-- url     : https://prove2.me/theorems/d4497839-1fe2-5355-aaa3-d315028e625a
-- title:
--   Quadratic Floor: is Unit int Cast of gcd
-- statement:
--   The Quadratic Floor construction uses the is Unit int Cast of gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L45-L49
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L45-L49

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.isUnit_intCast_of_gcd {A : ℕ} {B : ℤ} (h : Int.gcd B A = 1) : IsUnit (B : ZMod A) := by sorry

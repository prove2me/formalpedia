-- Prove2me | Theorems.Thm_QuadraticFloor_osum_mul_left
-- name    : QuadraticFloor.osum_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:58.809681+00:00
-- url     : https://prove2.me/theorems/11022a92-8d6b-4215-bb7a-600929810ebc
-- title:
--   Quadratic Floor: osum mul left
-- statement:
--   The Quadratic Floor construction uses the osum mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L64-L65
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L64-L65

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_mul_left (t c : ℤ) (g : ℤ → ℤ) : osum t (fun j => c * g j) = c * osum t g := by sorry

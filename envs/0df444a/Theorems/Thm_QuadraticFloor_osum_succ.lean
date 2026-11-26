-- Prove2me | Theorems.Thm_QuadraticFloor_osum_succ
-- name    : QuadraticFloor.osum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:03.623672+00:00
-- url     : https://prove2.me/theorems/69288b1d-1de7-5f49-ac00-15811c9a6308
-- title:
--   Quadratic Floor: osum succ
-- statement:
--   The Quadratic Floor construction uses the osum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L36-L44
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L36-L44

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_succ (t : ℤ) (g : ℤ → ℤ) : osum (t + 1) g = osum t g + g t := by sorry

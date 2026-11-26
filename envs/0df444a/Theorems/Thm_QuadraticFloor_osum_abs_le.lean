-- Prove2me | Theorems.Thm_QuadraticFloor_osum_abs_le
-- name    : QuadraticFloor.osum_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:22.575049+00:00
-- url     : https://prove2.me/theorems/01cd178d-ed75-53a9-93fd-e0946a745e4e
-- title:
--   Quadratic Floor: osum abs le
-- statement:
--   The Quadratic Floor construction uses the osum abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L78-L91
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L78-L91

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_abs_le (t : ℤ) (g : ℤ → ℤ) (hg : ∀ j, |g j| ≤ 1) : |osum t g| ≤ |t| := by sorry

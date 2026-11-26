-- Prove2me | Theorems.Thm_QuadraticFloor_osum_congr
-- name    : QuadraticFloor.osum_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:56.940547+00:00
-- url     : https://prove2.me/theorems/58ed2bcb-7734-469a-8acd-85654d03f1ed
-- title:
--   Quadratic Floor: osum congr
-- statement:
--   The Quadratic Floor construction uses the osum congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L93-L103
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L93-L103

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_congr {t : ℤ} {g g' : ℤ → ℤ} (h : ∀ j, |j| ≤ |t| → g j = g' j) :
    osum t g = osum t g' := by sorry

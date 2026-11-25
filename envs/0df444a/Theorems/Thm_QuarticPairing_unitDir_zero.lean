-- Prove2me | Theorems.Thm_QuarticPairing_unitDir_zero
-- name    : QuarticPairing.unitDir_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:11.062609+00:00
-- url     : https://prove2.me/theorems/3fca804d-fd8f-4b7d-881e-10db65969b87
-- title:
--   Quartic Pairing: unit Dir zero
-- statement:
--   The Quartic Pairing construction uses the unit Dir zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L57-L57
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L57-L57

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.unitDir_zero : unitDir 0 = 0 := by sorry

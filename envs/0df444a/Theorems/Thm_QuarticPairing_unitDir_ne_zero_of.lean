-- Prove2me | Theorems.Thm_QuarticPairing_unitDir_ne_zero_of
-- name    : QuarticPairing.unitDir_ne_zero_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:18.314567+00:00
-- url     : https://prove2.me/theorems/356acf16-6e4e-4461-bd31-52cf7c88c439
-- title:
--   Quartic Pairing: unit Dir ne zero of
-- statement:
--   The Quartic Pairing construction uses the unit Dir ne zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L121-L123
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L121-L123

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.unitDir_ne_zero_of {g κ : ℂ} {c : GaussianInt} (hg : g ≠ 0) (h : g ^ 2 = -κ * unitDir c) :
    unitDir c ≠ 0 := by sorry

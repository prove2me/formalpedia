-- Prove2me | Theorems.Thm_QuarticPairing_norm_unitDir
-- name    : QuarticPairing.norm_unitDir
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:00.433936+00:00
-- url     : https://prove2.me/theorems/8b9ad5c0-ccd2-54a8-b0fa-016b053641c4
-- title:
--   Quartic Pairing: norm unit Dir
-- statement:
--   The Quartic Pairing construction uses the norm unit Dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L53-L55
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L53-L55

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.norm_unitDir {c : GaussianInt} (hc : c ≠ 0) : ‖unitDir c‖ = 1 := by sorry

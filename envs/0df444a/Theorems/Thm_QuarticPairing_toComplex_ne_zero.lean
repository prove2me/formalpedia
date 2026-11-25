-- Prove2me | Theorems.Thm_QuarticPairing_toComplex_ne_zero
-- name    : QuarticPairing.toComplex_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:27.280877+00:00
-- url     : https://prove2.me/theorems/57f5672a-0dad-467a-abff-3a91b8c88b09
-- title:
--   Quartic Pairing: to Complex ne zero
-- statement:
--   The Quartic Pairing construction uses the to Complex ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L50-L51
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L50-L51

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.toComplex_ne_zero {c : GaussianInt} (hc : c ≠ 0) : GaussianInt.toComplex c ≠ 0 := by sorry

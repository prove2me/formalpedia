-- Prove2me | Theorems.Thm_P2M_FixedNumerator_norm_pow__cb22f6c8b435
-- name    : P2M_FixedNumerator_norm_pow__cb22f6c8b435
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:14.093096+00:00
-- url     : https://prove2.me/theorems/eddc5745-db04-46f3-8152-69d16136d495
-- title:
--   P2 M Fixed Numerator norm pow  cb22f6c8b435: P2 M Fixed Numerator norm pow  cb22f6c8b435
-- statement:
--   The P2 M Fixed Numerator norm pow  cb22f6c8b435 construction uses the P2 M Fixed Numerator norm pow  cb22f6c8b435 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L45-L48
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L45-L48

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem P2M_FixedNumerator_norm_pow__cb22f6c8b435 (a : GaussianInt) (k : ℕ) : (a ^ k).norm = a.norm ^ k := by sorry

alias «FixedNumerator».«norm_pow'» := P2M_FixedNumerator_norm_pow__cb22f6c8b435

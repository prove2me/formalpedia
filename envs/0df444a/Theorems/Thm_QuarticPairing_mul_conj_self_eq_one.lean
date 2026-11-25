-- Prove2me | Theorems.Thm_QuarticPairing_mul_conj_self_eq_one
-- name    : QuarticPairing.mul_conj_self_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:09.8968+00:00
-- url     : https://prove2.me/theorems/f405e1a9-f1f9-4636-b66f-171336d8dcfb
-- title:
--   Quartic Pairing: mul conj self eq one
-- statement:
--   The Quartic Pairing construction uses the mul conj self eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L30-L31

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.mul_conj_self_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * starRingEnd ℂ z = 1 := by sorry

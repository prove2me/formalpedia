-- Prove2me | Theorems.Thm_QuarticPairing_isBigO_neg_mul_conj
-- name    : QuarticPairing.isBigO_neg_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:40.76362+00:00
-- url     : https://prove2.me/theorems/1285b966-9692-4f6e-81f5-2ec9d4f0aaea
-- title:
--   Quartic Pairing: is Big O neg mul conj
-- statement:
--   The Quartic Pairing construction uses the is Big O neg mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L26-L31
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L26-L31

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.isBigO_neg_mul_conj {κ : ℂ} (hκ : ‖κ‖ = 1) {f : ℕ → ℂ} {u : ℕ → ℝ}
    (h : f =O[atTop] u) : (fun X => -κ * starRingEnd ℂ (f X)) =O[atTop] u := by sorry

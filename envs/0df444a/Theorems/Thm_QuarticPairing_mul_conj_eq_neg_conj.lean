-- Prove2me | Theorems.Thm_QuarticPairing_mul_conj_eq_neg_conj
-- name    : QuarticPairing.mul_conj_eq_neg_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:12.839814+00:00
-- url     : https://prove2.me/theorems/2e8c9361-24c3-47e8-9a94-2b94b6bd398b
-- title:
--   Quartic Pairing: mul conj eq neg conj
-- statement:
--   If `|θ| = |κ| = 1` and `g² = -κθ` (or `g = 0`), then `g θ̄ = -κ ḡ`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L34-L48
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L34-L48

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.mul_conj_eq_neg_conj {g θ κ : ℂ} (hθ : ‖θ‖ = 1) (hκ : ‖κ‖ = 1)
    (h : g = 0 ∨ g ^ 2 = -κ * θ) : g * starRingEnd ℂ θ = -κ * starRingEnd ℂ g := by sorry

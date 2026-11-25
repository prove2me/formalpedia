-- Prove2me | Theorems.Thm_QuarticPairing_term_pairing
-- name    : QuarticPairing.term_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:17.632432+00:00
-- url     : https://prove2.me/theorems/be92d1c2-40ec-4c68-9ed8-70e25d1492dc
-- title:
--   Quartic Pairing: term pairing
-- statement:
--   **The pointwise pairing.** If `g̃(c) = 0` or `g̃(c)² = -κ c/|c|` with `|κ| = 1`, then
--   `g̃(c) (c̄/|c|) = -κ conj g̃(c)`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L66-L76
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L66-L76

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.term_pairing {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g := by sorry

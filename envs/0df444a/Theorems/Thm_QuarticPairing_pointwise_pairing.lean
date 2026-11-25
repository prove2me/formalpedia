-- Prove2me | Theorems.Thm_QuarticPairing_pointwise_pairing
-- name    : QuarticPairing.pointwise_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:17.076885+00:00
-- url     : https://prove2.me/theorems/c1333684-9720-5c04-9f71-5cad1d2adb15
-- title:
--   Quartic Pairing: pointwise pairing
-- statement:
--   **The pointwise pairing.** If `g̃(c) = 0` or `g̃(c)² = -κ c/|c|` with `|κ| = 1`, then
--   `g̃(c) (c̄/|c|) = -κ conj g̃(c)`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L23-L26
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L23-L26

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.pointwise_pairing {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g := by sorry

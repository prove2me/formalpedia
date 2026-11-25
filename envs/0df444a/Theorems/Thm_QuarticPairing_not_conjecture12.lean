-- Prove2me | Theorems.Thm_QuarticPairing_not_conjecture12
-- name    : QuarticPairing.not_conjecture12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:35:45.144812+00:00
-- url     : https://prove2.me/theorems/9f5d1a80-2ab0-4e55-8466-6e6d8b6b360f
-- title:
--   Quartic Pairing: not conjecture12
-- statement:
--   **Conjecture 1.2 of David, Dunn, Hamieh and Lin is inconsistent with their identity (1.2).**
--   If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`, for a fixed unit `κ`, then the
--   cases `ℓ = 0` and `ℓ = 1` of the conjecture force `b_β = 0`, which the conjecture excludes.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L66-L73
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L66-L73

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.not_conjecture12 (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β := by sorry

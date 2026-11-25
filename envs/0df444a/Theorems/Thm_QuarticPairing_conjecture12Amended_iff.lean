-- Prove2me | Theorems.Thm_QuarticPairing_conjecture12Amended_iff
-- name    : QuarticPairing.conjecture12Amended_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:45.146796+00:00
-- url     : https://prove2.me/theorems/fe3c05ff-b4c8-4165-9497-91f810e492de
-- title:
--   Quartic Pairing: conjecture12 Amended iff
-- statement:
--   **The amended conjecture is consistent with the identity.** If `g̃(c)² = -κ c/|c|` (or
--   `g̃(c) = 0`) on the support of `Λ`, the amended conjecture is equivalent to its cases `ℓ ≤ 0`: the
--   cases `ℓ ≥ 1` follow from them.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L76-L90
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L76-L90

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.conjecture12Amended_iff (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    Conjecture12Amended g Λ β κ ↔
      ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ, ℓ ≤ 0 →
        (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
          =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by sorry

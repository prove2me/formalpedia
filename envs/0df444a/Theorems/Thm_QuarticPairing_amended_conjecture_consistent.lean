-- Prove2me | Theorems.Thm_QuarticPairing_amended_conjecture_consistent
-- name    : QuarticPairing.amended_conjecture_consistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:51.039798+00:00
-- url     : https://prove2.me/theorems/f1fb9228-a4e5-4ad0-a2a0-50120460e888
-- title:
--   Quartic Pairing: amended conjecture consistent
-- statement:
--   **The amended conjecture is consistent with the identity.** If `g̃(c)² = -κ c/|c|` (or
--   `g̃(c) = 0`) on the support of `Λ`, the amended conjecture is equivalent to its cases `ℓ ≤ 0`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L86-L93
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L86-L93

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.amended_conjecture_consistent (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    Conjecture12Amended g Λ β κ ↔
      ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ, ℓ ≤ 0 →
        (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
          =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by sorry

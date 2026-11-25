-- Prove2me | Theorems.Thm_QuarticPairing_twistedSum_reflect
-- name    : QuarticPairing.twistedSum_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:43.413132+00:00
-- url     : https://prove2.me/theorems/78779019-25af-55de-b009-22742bd2424e
-- title:
--   Quartic Pairing: twisted Sum reflect
-- statement:
--   **The reflection of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of
--   `Λ`, then `S_β(X; 1 - ℓ) = -κ conj S_β(X; ℓ)` for every `X` and every `ℓ ∈ ℤ`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L157-L162
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L157-L162

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
open Classical

theorem QuarticPairing.twistedSum_reflect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) (ℓ : ℤ) :
    twistedSum g Λ β X (1 - ℓ) = -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ) := by sorry

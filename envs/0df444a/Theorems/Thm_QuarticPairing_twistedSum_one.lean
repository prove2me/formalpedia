-- Prove2me | Theorems.Thm_QuarticPairing_twistedSum_one
-- name    : QuarticPairing.twistedSum_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:24.102823+00:00
-- url     : https://prove2.me/theorems/e8fcb89c-fce5-5396-896b-53bf36d1c22c
-- title:
--   Quartic Pairing: twisted Sum one
-- statement:
--   **The pairing of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`,
--   with `κ` a fixed unit, then `S_β(X; 1) = -κ conj S_β(X; 0)` for every `X`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L91-L97
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L91-L97

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

theorem QuarticPairing.twistedSum_one (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) := by sorry

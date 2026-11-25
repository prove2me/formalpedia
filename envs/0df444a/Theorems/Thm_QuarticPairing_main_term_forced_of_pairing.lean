-- Prove2me | Theorems.Thm_QuarticPairing_main_term_forced_of_pairing
-- name    : QuarticPairing.main_term_forced_of_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:51.248324+00:00
-- url     : https://prove2.me/theorems/bf8b2a6a-090a-41b6-99c7-ab55c2454738
-- title:
--   Quartic Pairing: main term forced of pairing
-- statement:
--   **The main term at `ℓ = 1` is forced.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support
--   of `Λ`, and `S_β(X; 0) = b X^{3/4} + O(X^{1/2+ε})` and `S_β(X; 1) = b' X^{3/4} + O(X^{1/2+ε})`
--   for every `ε > 0`, then `b' = -κ conj b`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L95-L111
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L95-L111

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.main_term_forced_of_pairing (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b b' : ℂ)
    (h0 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 0 -
      b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)))
    (h1 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 1 -
      b' * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    b' = -κ * starRingEnd ℂ b := by sorry

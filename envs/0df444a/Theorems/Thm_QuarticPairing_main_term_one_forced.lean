-- Prove2me | Theorems.Thm_QuarticPairing_main_term_one_forced
-- name    : QuarticPairing.main_term_one_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:58.411249+00:00
-- url     : https://prove2.me/theorems/89691eed-5828-591a-82b8-14491bf87585
-- title:
--   Quartic Pairing: main term one forced
-- statement:
--   **The main term at `ℓ = 1` is forced.** Under the identity, main terms `b X^{3/4}` at `ℓ = 0`
--   and `b' X^{3/4}` at `ℓ = 1`, with errors `O(X^{1/2+ε})` for every `ε > 0`, force
--   `b' = -κ conj b`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L98-L107
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L98-L107

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.main_term_one_forced (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b b' : ℂ)
    (h0 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 0 -
      b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[Filter.atTop]
        (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)))
    (h1 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 1 -
      b' * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[Filter.atTop]
        (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    b' = -κ * starRingEnd ℂ b := by sorry

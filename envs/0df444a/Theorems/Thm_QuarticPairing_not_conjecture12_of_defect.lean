-- Prove2me | Theorems.Thm_QuarticPairing_not_conjecture12_of_defect
-- name    : QuarticPairing.not_conjecture12_of_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:35:07.966049+00:00
-- url     : https://prove2.me/theorems/8d118d67-896a-5573-8640-081d51d6b6eb
-- title:
--   Quartic Pairing: not conjecture12 of defect
-- statement:
--   **The same with an exceptional set.** If the identity holds off a set `E` whose weight
--   `∑_{c ∈ E, N(c) ≤ X, c ≡ β} |g(c)| |Λ(c)|` is `O(X^{1/2+ε})` for every `ε > 0`, Conjecture 1.2
--   fails for the class `β`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L78-L101
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L78-L101

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.not_conjecture12_of_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β := by sorry

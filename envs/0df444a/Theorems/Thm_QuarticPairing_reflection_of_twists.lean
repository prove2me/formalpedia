-- Prove2me | Theorems.Thm_QuarticPairing_reflection_of_twists
-- name    : QuarticPairing.reflection_of_twists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:38.745888+00:00
-- url     : https://prove2.me/theorems/7f030283-309f-436c-a393-862e9f4b629a
-- title:
--   Quartic Pairing: reflection of twists
-- statement:
--   **The reflection of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of
--   `Λ`, then `S_β(X; 1 - ℓ) = -κ conj S_β(X; ℓ)` for every `X` and every `ℓ ∈ ℤ`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L78-L82
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L78-L82

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.reflection_of_twists (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ)
    (ℓ : ℤ) :
    twistedSum g Λ β X (1 - ℓ) = -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ) := by sorry

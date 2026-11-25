-- Prove2me | Theorems.Thm_QuarticPairing_pairing_of_twists_defect
-- name    : QuarticPairing.pairing_of_twists_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:28.196799+00:00
-- url     : https://prove2.me/theorems/176dd59c-ee35-5034-94e0-b578b17ec2cf
-- title:
--   Quartic Pairing: pairing of twists defect
-- statement:
--   **The pairing with an exceptional set.** If the identity holds off a set `E`, then
--   `|S_β(X; 1) + κ conj S_β(X; 0)|` is at most twice the weight of `E`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L37-L42
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L37-L42

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.pairing_of_twists_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X := by sorry

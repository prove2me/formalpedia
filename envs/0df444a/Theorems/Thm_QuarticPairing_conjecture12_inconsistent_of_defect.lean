-- Prove2me | Theorems.Thm_QuarticPairing_conjecture12_inconsistent_of_defect
-- name    : QuarticPairing.conjecture12_inconsistent_of_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:42.35369+00:00
-- url     : https://prove2.me/theorems/5438dee8-e5ae-5030-bb0d-6aecaf99d6ea
-- title:
--   Quartic Pairing: conjecture12 inconsistent of defect
-- statement:
--   **The same with an exceptional set** of weight `O(X^{1/2+ε})` for every `ε > 0`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L68-L74
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L68-L74

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.conjecture12_inconsistent_of_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β := by sorry

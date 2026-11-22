-- Prove2me | Theorems.Thm_Pseudorandom_exp_step_le
-- name    : Pseudorandom.exp_step_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:39.794816+00:00
-- url     : https://prove2.me/theorems/025fa2f6-bade-46f0-bd79-573857c6b154
-- title:
--   Pseudorandom: exp step le
-- statement:
--   One step of the exponential supermartingale.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L209-L242
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L209-L242

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}

theorem Pseudorandom.exp_step_le (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (Δ : α → ℝ)
    (hmean : ∑ a, p a * Δ a = 0) (C θ : ℝ) (hθ : 0 ≤ θ) (hθC : θ * C < 1)
    (hΔ : ∀ a, p a ≠ 0 → |Δ a| ≤ C) :
    ∑ a, p a * Real.exp (θ * Δ a) ≤
      Real.exp (θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a|) := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_IsExposureMartingale_pE_eq
-- name    : Pseudorandom.IsExposureMartingale.pE_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:18.453805+00:00
-- url     : https://prove2.me/theorems/ffb48190-5018-4dcb-a2c2-00cc70bcb018
-- title:
--   Is Exposure Martingale: p E eq
-- statement:
--   The expectation of the final value of an exposure martingale is its initial value.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L250-L260
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L250-L260

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

theorem Pseudorandom.IsExposureMartingale.pE_eq (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (ω₀ : Fin n → α) : ∀ k, k ≤ n → pE P (X k) = X 0 ω₀
  := by sorry

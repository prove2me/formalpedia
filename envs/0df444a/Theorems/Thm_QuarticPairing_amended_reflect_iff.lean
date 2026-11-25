-- Prove2me | Theorems.Thm_QuarticPairing_amended_reflect_iff
-- name    : QuarticPairing.amended_reflect_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:27.326828+00:00
-- url     : https://prove2.me/theorems/45c4684e-9973-5a6c-af02-f32e013c23e6
-- title:
--   Quartic Pairing: amended reflect iff
-- statement:
--   Under the identity, the error of the amended conjecture at `1 - ℓ` is `-κ` times the conjugate
--   of the error at `ℓ`, so the two are `O` of the same function together.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L53-L71
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L53-L71

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.amended_reflect_iff (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b : ℂ)
    (u : ℕ → ℝ) (ℓ : ℤ) :
    (fun X : ℕ => twistedSum g Λ β X (1 - ℓ) - amendedMain κ b X (1 - ℓ)) =O[atTop] u ↔
      (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) =O[atTop] u := by sorry

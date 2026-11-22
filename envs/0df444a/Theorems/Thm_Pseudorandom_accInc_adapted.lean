-- Prove2me | Theorems.Thm_Pseudorandom_accInc_adapted
-- name    : Pseudorandom.accInc_adapted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:30.703384+00:00
-- url     : https://prove2.me/theorems/24287a54-2205-46d2-9acc-46439181d546
-- title:
--   Pseudorandom: acc Inc adapted
-- statement:
--   The Pseudorandom construction uses the acc Inc adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L167-L181
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L167-L181

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

theorem Pseudorandom.accInc_adapted (hX : ∀ k, Adapted k (X k)) (hG : ∀ k, Adapted k (G k)) :
    ∀ k, Adapted k (accInc P X G k)
  := by sorry

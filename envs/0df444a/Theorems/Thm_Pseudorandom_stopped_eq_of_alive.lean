-- Prove2me | Theorems.Thm_Pseudorandom_stopped_eq_of_alive
-- name    : Pseudorandom.stopped_eq_of_alive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:18.454074+00:00
-- url     : https://prove2.me/theorems/2a7a5f4f-c2ec-4be1-b98d-980a67240311
-- title:
--   Pseudorandom: stopped eq of alive
-- statement:
--   The Pseudorandom construction uses the stopped eq of alive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L132-L140
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L132-L140

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
omit [Fintype α]

theorem Pseudorandom.stopped_eq_of_alive {ω : Fin n → α} :
    ∀ k, (k = 0 ∨ Alive G (k - 1) ω) → stopped X G k ω = X k ω
  := by sorry

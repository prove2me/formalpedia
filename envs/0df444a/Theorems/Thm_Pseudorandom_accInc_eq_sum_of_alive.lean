-- Prove2me | Theorems.Thm_Pseudorandom_accInc_eq_sum_of_alive
-- name    : Pseudorandom.accInc_eq_sum_of_alive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:31.706363+00:00
-- url     : https://prove2.me/theorems/f364b28e-6190-4aa5-ba23-08c7341cfdc0
-- title:
--   Pseudorandom: acc Inc eq sum of alive
-- statement:
--   The Pseudorandom construction uses the acc Inc eq sum of alive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L194-L206
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L194-L206

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

theorem Pseudorandom.accInc_eq_sum_of_alive {ω : Fin n → α} (hall : ∀ i : Fin n, G i ω) :
    ∀ k, k ≤ n → accInc P X G k ω =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), condAbsInc P X i ω
  := by sorry

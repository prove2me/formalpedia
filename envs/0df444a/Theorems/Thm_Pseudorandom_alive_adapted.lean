-- Prove2me | Theorems.Thm_Pseudorandom_alive_adapted
-- name    : Pseudorandom.alive_adapted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:56.014213+00:00
-- url     : https://prove2.me/theorems/a25d5978-6da8-4ec8-8f79-2c4ef1b583e7
-- title:
--   Pseudorandom: alive adapted
-- statement:
--   The Pseudorandom construction uses the alive adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L118-L129
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L118-L129

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

theorem Pseudorandom.alive_adapted (hG : ∀ k, Adapted k (G k)) (k : ℕ) :
    Adapted k (fun ω => Alive G k ω) := by sorry

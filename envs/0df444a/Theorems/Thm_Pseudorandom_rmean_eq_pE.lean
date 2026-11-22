-- Prove2me | Theorems.Thm_Pseudorandom_rmean_eq_pE
-- name    : Pseudorandom.rmean_eq_pE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:32.020168+00:00
-- url     : https://prove2.me/theorems/24cd223a-75dc-4ad0-ac01-db78bde2baa9
-- title:
--   Pseudorandom: rmean eq p E
-- statement:
--   The Pseudorandom construction uses the rmean eq p E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L207-L224
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L207-L224

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]

theorem Pseudorandom.rmean_eq_pE : ∀ {n : ℕ} (P : Fin n → α → ℝ) (f : (Fin n → α) → ℝ),
    rmean P f = pE P f
  := by sorry

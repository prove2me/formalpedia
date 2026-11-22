-- Prove2me | Theorems.Thm_Pseudorandom_pE_sum
-- name    : Pseudorandom.pE_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:56.283802+00:00
-- url     : https://prove2.me/theorems/a7d95a26-de60-4f8e-9c6a-6aa9b43b4880
-- title:
--   Pseudorandom: p E sum
-- statement:
--   The Pseudorandom construction uses the p E sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L76-L80
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L76-L80

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}

theorem Pseudorandom.pE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → α) → ℝ) :
    pE P (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, pE P (f k) := by sorry

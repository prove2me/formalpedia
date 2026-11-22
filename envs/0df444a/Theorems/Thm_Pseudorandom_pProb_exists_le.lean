-- Prove2me | Theorems.Thm_Pseudorandom_pProb_exists_le
-- name    : Pseudorandom.pProb_exists_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:46.235053+00:00
-- url     : https://prove2.me/theorems/173c4ea1-a83c-45aa-a64b-aea6898691e1
-- title:
--   Pseudorandom: p Prob exists le
-- statement:
--   Union bound.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L142-L154
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L142-L154

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

theorem Pseudorandom.pProb_exists_le {κ : Type*} (hP : IsPMF P) (s : Finset κ) (S : κ → (ι → α) → Prop) :
    pProb P (fun ω => ∃ k ∈ s, S k ω) ≤ ∑ k ∈ s, pProb P (S k) := by sorry

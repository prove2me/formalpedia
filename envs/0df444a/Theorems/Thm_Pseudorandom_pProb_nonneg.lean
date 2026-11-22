-- Prove2me | Theorems.Thm_Pseudorandom_pProb_nonneg
-- name    : Pseudorandom.pProb_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:21.811414+00:00
-- url     : https://prove2.me/theorems/60001752-63ac-4b75-83ac-bf23accb8540
-- title:
--   Pseudorandom: p Prob nonneg
-- statement:
--   The Pseudorandom construction uses the p Prob nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L121-L124
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L121-L124

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

theorem Pseudorandom.pProb_nonneg (hP : IsPMF P) (S : (ι → α) → Prop) : 0 ≤ pProb P S := by sorry

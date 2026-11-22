-- Prove2me | Theorems.Thm_Pseudorandom_pProb_or_le
-- name    : Pseudorandom.pProb_or_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:09.742808+00:00
-- url     : https://prove2.me/theorems/93b58547-d9d8-4d11-a060-2b6cdf331bb3
-- title:
--   Pseudorandom: p Prob or le
-- statement:
--   The Pseudorandom construction uses the p Prob or le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L156-L162
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L156-L162

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

theorem Pseudorandom.pProb_or_le (hP : IsPMF P) (S T : (ι → α) → Prop) :
    pProb P (fun ω => S ω ∨ T ω) ≤ pProb P S + pProb P T := by sorry

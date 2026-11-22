-- Prove2me | Theorems.Thm_Pseudorandom_pProb_mono
-- name    : Pseudorandom.pProb_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:12.301431+00:00
-- url     : https://prove2.me/theorems/05b28b97-71fc-429e-9f6d-dde45a6a6e80
-- title:
--   Pseudorandom: p Prob mono
-- statement:
--   The Pseudorandom construction uses the p Prob mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L132-L139
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L132-L139

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

theorem Pseudorandom.pProb_mono (hP : IsPMF P) {S T : (ι → α) → Prop} (h : ∀ ω, S ω → T ω) :
    pProb P S ≤ pProb P T := by sorry

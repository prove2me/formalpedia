-- Prove2me | Theorems.Thm_Pseudorandom_pProb_le_one
-- name    : Pseudorandom.pProb_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:38.081838+00:00
-- url     : https://prove2.me/theorems/e0d952db-cf4d-44f0-9b7e-ad3bd52c2f20
-- title:
--   Pseudorandom: p Prob le one
-- statement:
--   The Pseudorandom construction uses the p Prob le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L126-L130
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L126-L130

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

theorem Pseudorandom.pProb_le_one (hP : IsPMF P) (S : (ι → α) → Prop) : pProb P S ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_pProb_not
-- name    : Pseudorandom.pProb_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:12.721675+00:00
-- url     : https://prove2.me/theorems/baaefabc-002c-4ed2-b937-4f188b265206
-- title:
--   Pseudorandom: p Prob not
-- statement:
--   The Pseudorandom construction uses the p Prob not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L164-L172
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L164-L172

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

theorem Pseudorandom.pProb_not (hP : IsPMF P) (S : (ι → α) → Prop) :
    pProb P (fun ω => ¬ S ω) = 1 - pProb P S := by sorry

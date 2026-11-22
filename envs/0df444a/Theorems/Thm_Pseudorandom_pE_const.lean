-- Prove2me | Theorems.Thm_Pseudorandom_pE_const
-- name    : Pseudorandom.pE_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:21.546793+00:00
-- url     : https://prove2.me/theorems/02721d38-9fcc-4c73-a9f3-95dcd728761d
-- title:
--   Pseudorandom: p E const
-- statement:
--   The Pseudorandom construction uses the p E const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L53-L55
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L53-L55

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

theorem Pseudorandom.pE_const (hP : IsPMF P) (c : ℝ) : pE P (fun _ => c) = c := by sorry

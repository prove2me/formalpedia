-- Prove2me | Theorems.Thm_Pseudorandom_pE_neg
-- name    : Pseudorandom.pE_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:57.404794+00:00
-- url     : https://prove2.me/theorems/c4d590e7-751e-4deb-9bf7-99dc219b7dfe
-- title:
--   Pseudorandom: p E neg
-- statement:
--   The Pseudorandom construction uses the p E neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L72-L74
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L72-L74

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

theorem Pseudorandom.pE_neg (f : (ι → α) → ℝ) : pE P (fun ω => -f ω) = -pE P f := by sorry

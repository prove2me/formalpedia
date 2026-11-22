-- Prove2me | Theorems.Thm_Pseudorandom_pE_nonneg
-- name    : Pseudorandom.pE_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:04.6438+00:00
-- url     : https://prove2.me/theorems/079ac2d1-9713-4c47-98f1-ce38433c41b9
-- title:
--   Pseudorandom: p E nonneg
-- statement:
--   The Pseudorandom construction uses the p E nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L94-L96
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L94-L96

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

theorem Pseudorandom.pE_nonneg (hP : IsPMF P) {f : (ι → α) → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ pE P f := by sorry

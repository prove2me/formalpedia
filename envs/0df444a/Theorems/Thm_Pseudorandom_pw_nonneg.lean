-- Prove2me | Theorems.Thm_Pseudorandom_pw_nonneg
-- name    : Pseudorandom.pw_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:58.947425+00:00
-- url     : https://prove2.me/theorems/9c701a23-6e70-4db9-9722-07499a4f86f8
-- title:
--   Pseudorandom: pw nonneg
-- statement:
--   The Pseudorandom construction uses the pw nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L45-L46
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L45-L46

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
omit [DecidableEq ι]

theorem Pseudorandom.pw_nonneg (hP : IsPMF P) (ω : ι → α) : 0 ≤ pw P ω := by sorry

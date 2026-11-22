-- Prove2me | Theorems.Thm_Pseudorandom_sum_pw
-- name    : Pseudorandom.sum_pw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:33.640944+00:00
-- url     : https://prove2.me/theorems/c233126d-e29f-4d18-8674-4799a018c4b8
-- title:
--   Pseudorandom: sum pw
-- statement:
--   The Pseudorandom construction uses the sum pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L48-L51
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L48-L51

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

theorem Pseudorandom.sum_pw (hP : IsPMF P) : ∑ ω, pw P ω = 1 := by sorry

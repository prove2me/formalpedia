-- Prove2me | Theorems.Thm_Pseudorandom_pE_sub
-- name    : Pseudorandom.pE_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:33.093732+00:00
-- url     : https://prove2.me/theorems/6fab65a9-9a65-45bd-87b6-f0e169d4657e
-- title:
--   Pseudorandom: p E sub
-- statement:
--   The Pseudorandom construction uses the p E sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L62-L65
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L62-L65

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

theorem Pseudorandom.pE_sub (f g : (ι → α) → ℝ) : pE P (fun ω => f ω - g ω) = pE P f - pE P g := by sorry

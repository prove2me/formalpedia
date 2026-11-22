-- Prove2me | Theorems.Thm_Pseudorandom_pE_const_mul
-- name    : Pseudorandom.pE_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:33.641854+00:00
-- url     : https://prove2.me/theorems/9e80b029-9ff1-4e4e-b02a-6932c2e8e7ef
-- title:
--   Pseudorandom: p E const mul
-- statement:
--   The Pseudorandom construction uses the p E const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L67-L70
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L67-L70

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

theorem Pseudorandom.pE_const_mul (c : ℝ) (f : (ι → α) → ℝ) : pE P (fun ω => c * f ω) = c * pE P f := by sorry

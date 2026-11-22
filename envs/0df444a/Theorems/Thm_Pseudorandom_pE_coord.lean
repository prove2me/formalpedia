-- Prove2me | Theorems.Thm_Pseudorandom_pE_coord
-- name    : Pseudorandom.pE_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:20.407797+00:00
-- url     : https://prove2.me/theorems/856aa429-e9e0-4a9c-a51a-6469fa83e6bb
-- title:
--   Pseudorandom: p E coord
-- statement:
--   Expectation of a function of a single coordinate.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L107-L119
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L107-L119

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

theorem Pseudorandom.pE_coord (hP : IsPMF P) (i : ι) (g : α → ℝ) :
    pE P (fun ω => g (ω i)) = ∑ a, P i a * g a := by sorry

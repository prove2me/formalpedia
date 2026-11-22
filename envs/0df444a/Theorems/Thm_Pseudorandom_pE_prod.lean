-- Prove2me | Theorems.Thm_Pseudorandom_pE_prod
-- name    : Pseudorandom.pE_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:42.928498+00:00
-- url     : https://prove2.me/theorems/3e7e192b-7640-41b9-9c8e-1337dab7f783
-- title:
--   Pseudorandom: p E prod
-- statement:
--   Expectation of a product of functions of distinct coordinates (independence).
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L99-L104
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L99-L104

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

theorem Pseudorandom.pE_prod (g : ι → α → ℝ) :
    pE P (fun ω => ∏ i, g i (ω i)) = ∏ i, ∑ a, P i a * g i a := by sorry

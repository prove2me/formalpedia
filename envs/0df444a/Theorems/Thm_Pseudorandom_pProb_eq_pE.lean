-- Prove2me | Theorems.Thm_Pseudorandom_pProb_eq_pE
-- name    : Pseudorandom.pProb_eq_pE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:13.898567+00:00
-- url     : https://prove2.me/theorems/48705743-a4ea-4e77-a100-7ce3d9f29025
-- title:
--   Pseudorandom: p Prob eq p E
-- statement:
--   A probability is the expectation of any indicator function of the event.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L205-L212
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L205-L212

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

theorem Pseudorandom.pProb_eq_pE (S : (ι → α) → Prop) (g : (ι → α) → ℝ) (h1 : ∀ ω, S ω → g ω = 1)
    (h0 : ∀ ω, ¬ S ω → g ω = 0) : pProb P S = pE P g := by sorry

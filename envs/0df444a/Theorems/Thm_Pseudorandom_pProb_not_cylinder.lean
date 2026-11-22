-- Prove2me | Theorems.Thm_Pseudorandom_pProb_not_cylinder
-- name    : Pseudorandom.pProb_not_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:07.896797+00:00
-- url     : https://prove2.me/theorems/ecbb781e-f934-467b-ae20-7a6c404d8dd6
-- title:
--   Pseudorandom: p Prob not cylinder
-- statement:
--   Probability of the complement of a cylinder event.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L237-L239
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L237-L239

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

theorem Pseudorandom.pProb_not_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ¬ ∀ i ∈ S, ω i = x i) = 1 - ∏ i ∈ S, P i (x i) := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_pProb_cylinder
-- name    : Pseudorandom.pProb_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:21.327812+00:00
-- url     : https://prove2.me/theorems/b901af31-609b-4d1b-aeb7-3bc72685351f
-- title:
--   Pseudorandom: p Prob cylinder
-- statement:
--   Probability of a cylinder event: prescribed values on a finite set of coordinates.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L215-L234
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L215-L234

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

theorem Pseudorandom.pProb_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ∀ i ∈ S, ω i = x i) = ∏ i ∈ S, P i (x i) := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_exists_of_pProb_lt_one
-- name    : Pseudorandom.exists_of_pProb_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:45.910363+00:00
-- url     : https://prove2.me/theorems/355c0ef3-9d72-419c-a214-6f0b84da480e
-- title:
--   Pseudorandom: exists of p Prob lt one
-- statement:
--   If an event has probability `< 1`, some outcome of positive weight avoids it.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L175-L188
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L175-L188

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

theorem Pseudorandom.exists_of_pProb_lt_one (hP : IsPMF P) {S : (ι → α) → Prop} (h : pProb P S < 1) :
    ∃ ω, 0 < pw P ω ∧ ¬ S ω := by sorry

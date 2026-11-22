-- Prove2me | Theorems.Thm_Pseudorandom_pE_mono_supp
-- name    : Pseudorandom.pE_mono_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:09.260801+00:00
-- url     : https://prove2.me/theorems/11e6fcb3-686a-4cad-a05d-35e0d94ead0f
-- title:
--   Pseudorandom: p E mono supp
-- statement:
--   Monotonicity only needs the inequality on outcomes of positive weight.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L87-L92
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L87-L92

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

theorem Pseudorandom.pE_mono_supp (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, 0 < pw P ω → f ω ≤ g ω) :
    pE P f ≤ pE P g := by sorry

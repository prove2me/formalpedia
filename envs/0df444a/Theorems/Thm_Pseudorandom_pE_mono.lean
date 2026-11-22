-- Prove2me | Theorems.Thm_Pseudorandom_pE_mono
-- name    : Pseudorandom.pE_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:13.497599+00:00
-- url     : https://prove2.me/theorems/5b0d06f0-66d2-436b-9c09-a9414d56084f
-- title:
--   Pseudorandom: p E mono
-- statement:
--   The Pseudorandom construction uses the p E mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L82-L84
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L82-L84

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

theorem Pseudorandom.pE_mono (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    pE P f ≤ pE P g := by sorry

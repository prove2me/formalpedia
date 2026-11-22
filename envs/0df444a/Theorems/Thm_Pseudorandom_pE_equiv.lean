-- Prove2me | Theorems.Thm_Pseudorandom_pE_equiv
-- name    : Pseudorandom.pE_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:58.831817+00:00
-- url     : https://prove2.me/theorems/5198ffcd-1fc9-4713-a604-c91c81afd494
-- title:
--   Pseudorandom: p E equiv
-- statement:
--   The Pseudorandom construction uses the p E equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L253-L263
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L253-L263

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

theorem Pseudorandom.pE_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (f : (ι → α) → ℝ) :
    pE P f = pE (fun j => P (e.symm j)) (fun ω' => f (ω' ∘ e)) := by sorry

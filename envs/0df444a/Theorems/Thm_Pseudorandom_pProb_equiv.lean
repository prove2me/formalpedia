-- Prove2me | Theorems.Thm_Pseudorandom_pProb_equiv
-- name    : Pseudorandom.pProb_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:33.898556+00:00
-- url     : https://prove2.me/theorems/8b59cdc2-91fa-4978-b6ea-c0fe166b73fc
-- title:
--   Pseudorandom: p Prob equiv
-- statement:
--   The Pseudorandom construction uses the p Prob equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L265-L269
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L265-L269

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

theorem Pseudorandom.pProb_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (S : (ι → α) → Prop) :
    pProb P S = pProb (fun j => P (e.symm j)) (fun ω' => S (ω' ∘ e)) := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_pProb_congr
-- name    : Pseudorandom.pProb_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:13.897851+00:00
-- url     : https://prove2.me/theorems/9a8a1c04-1e3f-46c1-81ac-8941c9967756
-- title:
--   Pseudorandom: p Prob congr
-- statement:
--   The Pseudorandom construction uses the p Prob congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L241-L243
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L241-L243

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

theorem Pseudorandom.pProb_congr {S T : (ι → α) → Prop} (h : ∀ ω, S ω ↔ T ω) : pProb P S = pProb P T := by sorry

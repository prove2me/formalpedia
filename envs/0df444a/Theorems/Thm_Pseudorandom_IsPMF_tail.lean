-- Prove2me | Theorems.Thm_Pseudorandom_IsPMF_tail
-- name    : Pseudorandom.IsPMF.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:35.988806+00:00
-- url     : https://prove2.me/theorems/b5a88e45-26b6-43d9-9fab-e3182b7b2c22
-- title:
--   Is PMF: tail
-- statement:
--   The Is PMF construction uses the tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L226-L228
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L226-L228

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]

theorem Pseudorandom.IsPMF.tail {n : ℕ} {P : Fin (n + 1) → α → ℝ} (hP : IsPMF P) :
    IsPMF (fun i : Fin n => P i.succ) := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_pProb_ge_le_markov
-- name    : Pseudorandom.pProb_ge_le_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:59.131553+00:00
-- url     : https://prove2.me/theorems/6a1d9030-3bb4-4ffc-adc4-b44bd49aa688
-- title:
--   Pseudorandom: p Prob ge le markov
-- statement:
--   Probability of the event that a function is at least `t` is at most `E f / t`
--   (Markov's inequality, for nonnegative `f`).
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L192-L201
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean#L192-L201

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

theorem Pseudorandom.pProb_ge_le_markov (hP : IsPMF P) {f : (ι → α) → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ}
    (ht : 0 < t) : pProb P (fun ω => t ≤ f ω) ≤ pE P f / t := by sorry

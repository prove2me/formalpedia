-- Prove2me | Theorems.Thm_Pseudorandom_pE_lower_tail
-- name    : Pseudorandom.pE_lower_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:25.82839+00:00
-- url     : https://prove2.me/theorems/a52943d9-0c0f-4d69-980c-732635c5dee0
-- title:
--   Pseudorandom: p E lower tail
-- statement:
--   **Bernstein-type bounded differences, lower tail.**
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L396-L405
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L396-L405

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem Pseudorandom.pE_lower_tail (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ pE P f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by sorry

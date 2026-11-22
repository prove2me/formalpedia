-- Prove2me | Theorems.Thm_Pseudorandom_pE_upper_tail_fin
-- name    : Pseudorandom.pE_upper_tail_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:56.66531+00:00
-- url     : https://prove2.me/theorems/82dd9291-9e05-43e0-8cfa-1ee73a395389
-- title:
--   Pseudorandom: p E upper tail fin
-- statement:
--   The Pseudorandom construction uses the p E upper tail fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L339-L369
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L339-L369

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem Pseudorandom.pE_upper_tail_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by sorry

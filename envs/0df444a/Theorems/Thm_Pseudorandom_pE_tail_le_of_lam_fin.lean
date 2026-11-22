-- Prove2me | Theorems.Thm_Pseudorandom_pE_tail_le_of_lam_fin
-- name    : Pseudorandom.pE_tail_le_of_lam_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:40.13904+00:00
-- url     : https://prove2.me/theorems/e0a409b1-932f-4896-b8ff-a72746a42c5f
-- title:
--   Pseudorandom: p E tail le of lam fin
-- statement:
--   The Pseudorandom construction uses the p E tail le of lam fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L311-L337
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L311-L337

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem Pseudorandom.pE_tail_le_of_lam_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam t : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(lam * t) + lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by sorry

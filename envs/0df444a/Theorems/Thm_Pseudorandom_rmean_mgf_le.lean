-- Prove2me | Theorems.Thm_Pseudorandom_rmean_mgf_le
-- name    : Pseudorandom.rmean_mgf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:38.27378+00:00
-- url     : https://prove2.me/theorems/f9e22150-5d8c-4695-ad53-56ad9a5b781e
-- title:
--   Pseudorandom: rmean mgf le
-- statement:
--   Exponential moment bound for the centered function.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L231-L301
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L231-L301

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]

theorem Pseudorandom.rmean_mgf_le : ∀ {n : ℕ} (P : Fin n → α → ℝ) (_hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam : ℝ)
    (_hcL : ∀ i, c i ≤ L) (_hf : CoordGap f c) (_hfR : CoordRare f R)
    (_hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (_hlam : 0 ≤ lam) (_hlamL : lam * L < 1),
    rmean P (fun ω => Real.exp (lam * (f ω - rmean P f))) ≤
      Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L)))
  := by sorry

-- Prove2me | Theorems.Thm_Pseudorandom_freedman_two_sided
-- name    : Pseudorandom.freedman_two_sided
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:35.562808+00:00
-- url     : https://prove2.me/theorems/2ab026ca-3f34-4c96-a3c5-9680da167e81
-- title:
--   Pseudorandom: freedman two sided
-- statement:
--   **Freedman's inequality** (two-sided) for a stopped exposure martingale.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L391-L416
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L391-L416

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}

theorem Pseudorandom.freedman_two_sided (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ |X n ω - X 0 ω| ∧ ∀ i : Fin n, G i ω) ≤
      2 * Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by sorry

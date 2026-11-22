-- Prove2me | Theorems.Thm_Pseudorandom_freedman_upper
-- name    : Pseudorandom.freedman_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:42.159833+00:00
-- url     : https://prove2.me/theorems/47d462a2-0696-42cb-9ccf-eb7fd27ddee7
-- title:
--   Pseudorandom: freedman upper
-- statement:
--   **Freedman's inequality** (upper tail) for a stopped exposure martingale.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L263-L381
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L263-L381

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

theorem Pseudorandom.freedman_upper (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) ≤
      Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by sorry

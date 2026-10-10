-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_10
-- name    : WassFSG.Grad.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:27:26.870349+00:00
-- url     : https://prove2.me/theorems/8eb0aa60-9b40-488f-98a3-d9d08f09591e
-- title:
--   Lemma 10 — the largest root r₀ of B√r + A = r satisfies B² ≤ r₀ ≤ 2A + B²
-- statement:
--   Let $A,B>0$ and let $r_0\ge0$ be the largest non-negative solution of
--   $$
--   B\sqrt r + A = r .
--   $$
--   Then
--   $$
--   B^2\le r_0\le 2A+B^2 .
--   $$
--
--   This elementary bound (from Bartlett, Bousquet and Mendelson, p. 1512) locates the fixed point used in the proof of Theorem 3, where $A=\epsilon_n$ and $B=2\sqrt{r_{n\star}}$.
--
--   **Formalization Note** "The largest solution" is encoded as a non-negative solution that dominates every non-negative solution. (For $A,B>0$ the non-negative solution is in fact unique, so the maximality hypothesis is redundant.)
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 10, p. 26

import Mathlib

namespace WassFSG.Grad

theorem lemma_10 (A B r₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 ≤ r₀)
    (hsol : B * Real.sqrt r₀ + A = r₀)
    (hlargest : ∀ r : ℝ, 0 ≤ r → B * Real.sqrt r + A = r → r ≤ r₀) :
    B ^ 2 ≤ r₀ ∧ r₀ ≤ 2 * A + B ^ 2 := by sorry

end WassFSG.Grad

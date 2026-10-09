-- Prove2me | Theorems.Thm_WassFSG_Lip_lemma_10
-- name    : WassFSG.Lip.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:48:53.408021+00:00
-- url     : https://prove2.me/theorems/bd480dc7-e8fe-4b60-8f09-5ec3c68d81a1
-- title:
--   Lemma 10 — the largest root r₀ of B√r + A = r satisfies B² ≤ r₀ ≤ 2A + B²
-- statement:
--   Let $A, B > 0$, and let $r_0 \ge 0$ be the largest solution of
--   $$
--   B\sqrt r + A = r.
--   $$
--   Then
--   $$
--   B^2 \le r_0 \le 2A + B^2.
--   $$
--
--   The lemma bounds the fixed point used to choose the localization level in the proof of Theorem 2.
--
--   **Formalization Note** "The largest solution" is encoded as: $r_0\ge0$ solves the equation and every solution $r\ge0$ satisfies $r\le r_0$. The equation has exactly one non-negative solution, $r_0 = \big((B+\sqrt{B^2+4A})/2\big)^2$, so the maximality hypothesis is not needed for the conclusion; the hypotheses are satisfiable (e.g. $A = 2$, $B = 1$, $r_0 = 4$).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 10, p. 26 (citing Bartlett, Bousquet and Mendelson 2005, p. 1512)

import Mathlib

namespace WassFSG.Lip

theorem lemma_10 (A B r₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 ≤ r₀)
    (hsol : B * Real.sqrt r₀ + A = r₀)
    (hlargest : ∀ r : ℝ, 0 ≤ r → B * Real.sqrt r + A = r → r ≤ r₀) :
    B ^ 2 ≤ r₀ ∧ r₀ ≤ 2 * A + B ^ 2 := by sorry

end WassFSG.Lip

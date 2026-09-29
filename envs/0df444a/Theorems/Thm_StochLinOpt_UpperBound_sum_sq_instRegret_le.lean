-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_sum_sq_instRegret_le
-- name    : StochLinOpt.UpperBound.sum_sq_instRegret_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:31:04.008301+00:00
-- url     : https://prove2.me/theorems/bdb53bf7-6096-449f-9ed1-e8ae491181d6
-- title:
--   Theorem 6 (corrected) — $\sum_{t\le T}r_t^2\le8n\beta_T\ln(T+1)$ while $\mu\in B^2_t$
-- statement:
--   Let $D\subseteq[-1,1]^n$, let $\mu\in\mathbb R^n$ satisfy $|\mu^\top y|\le1$ for all $y\in D$, and let $x^*\in D$ minimise $\mu^\top y$ over $D$. Let $0<\delta<1$ with $\beta_1\ge1$, and let $(x_t)$ be a run of ConfidenceBall₂$(D,\delta)$ with losses $(\ell_t)$. Write $r_t=\mu^\top x_t-\mu^\top x^*$ for the instantaneous regret. If $\mu\in B^2_t$ for every $1\le t\le T$, then
--
--   $$\sum_{t=1}^{T}r_t^2\le8n\,\beta_T\ln(T+1).$$
--
--   This is the sum-of-squares regret bound: on the event that the confidence ellipsoids contain the true mean, the regret is controlled deterministically. Together with the confidence theorem (Theorem 5) and Cauchy–Schwarz, it gives the problem-independent upper bound.
--
--   **Formalization Note** The paper prints $8n\beta_T\ln T$; the proof, via Lemma 9, gives $8n\beta_T\ln(T+1)$, and the printed bound is false at $T=1$ (with $n=1$, $D=[-1,1]$, $\mu>0$, the tie-break $x_1=1$ gives $r_1^2=4\mu^2>0$). The paper's proof uses "$1<\beta_1$"; it is added as the hypothesis $\beta_1\ge1$, which holds whenever $n\ge1$ and $n\le\beta_1$. The statement is deterministic.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 7, Theorem 6 (ConfidenceBall2 bullet); proof PDF p. 8, Section 5.1

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem sum_sq_instRegret_le {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ₁ : 1 ≤ beta n δ 1)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (T : ℕ)
    (hμ : ∀ t ∈ Finset.Icc 1 T, μ ∈ confBall δ x ℓ t) :
    ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * n * beta n δ T * Real.log (T + 1) := by sorry

end StochLinOpt.UpperBound

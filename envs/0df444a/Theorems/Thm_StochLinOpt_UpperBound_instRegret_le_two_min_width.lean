-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_instRegret_le_two_min_width
-- name    : StochLinOpt.UpperBound.instRegret_le_two_min_width
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:29:10.851281+00:00
-- url     : https://prove2.me/theorems/a7cbe098-197c-468d-9898-4f947b045b89
-- title:
--   Lemma 8 — instantaneous regret at most $2\min(\sqrt{\beta_t}w_t,1)$
-- statement:
--   Let $D\subseteq\mathbb R^n$, let $\mu\in\mathbb R^n$ satisfy $|\mu^\top y|\le1$ for all $y\in D$, and let $x^*\in D$ minimise $\mu^\top y$ over $D$. Let $(x_t)$ be a run of ConfidenceBall₂$(D,\delta)$ with losses $(\ell_t)$, and let $w_t=\sqrt{x_t^\top A_t^{-1}x_t}$. Fix a round $t\ge1$. If $\mu\in B^2_t$, then the instantaneous regret $r_t=\mu^\top x_t-\mu^\top x^*$ satisfies
--
--   $$r_t\le2\min\big(\sqrt{\beta_t}\,w_t,\ 1\big).$$
--
--   This is the per-round step of the upper bound: while the confidence ellipsoid contains the true mean, the regret of a round is controlled by the width of the ellipsoid in the chosen direction.
--
--   **Formalization Note** The statement is deterministic (pathwise). Rounds are indexed from $1$. The bound by $2$ comes from $|\mu^\top y|\le1$ on $D$, which is the paper's assumption that expected costs lie in $[-1,1]$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 8, Lemma 8 (ConfidenceBall2 bullet)

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem instRegret_le_two_min_width {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (t : ℕ) (ht : 1 ≤ t)
    (hμ : μ ∈ confBall δ x ℓ t) :
    μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ 2 * min (Real.sqrt (beta n δ t) * width x t) 1 := by sorry

end StochLinOpt.UpperBound

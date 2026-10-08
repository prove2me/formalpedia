-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_stationary_gap_le
-- name    : PGLandscape.ApproxClosure.stationary_gap_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:09.895506+00:00
-- url     : https://prove2.me/theorems/71b1b849-1573-4bfa-a885-86b3dacc365c
-- title:
--   Theorem 5, p. 26 — every stationary point is within κε/(1−γ) of optimal
-- statement:
--   Consider a discounted-cost MDP with an optimal policy $\pi^*$ under Assumptions 1 and 2, and a parameterized policy class $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ with $\Theta\subseteq\mathbb R^d$ convex. Suppose Conditions 0 and 2.A hold, and Condition 5 holds with inherent Bellman error $\varepsilon\ge0$. Let $\kappa\ge0$ be any scalar satisfying (13), i.e. $\|J-J^*\|_{1,\rho}\le\frac{\kappa}{1-\gamma}\|J-TJ\|_{1,\rho}$ for every $J=J_{\pi_\theta}$, $\theta\in\Theta$ (so $\kappa\ge\kappa_\rho$). Then $\ell(\theta)=\ell(\pi_\theta)$ is continuously differentiable near every $\theta\in\Theta$, and every stationary point $\theta$ of $\ell$ on $\Theta$ satisfies
--
--   $$
--   \ell(\pi_\theta)-\ell(\pi^*)\le\frac{\kappa}{1-\gamma}\cdot\varepsilon .
--   $$
--
--   Policy gradient methods therefore reach near-optimal policies even when the policy class is only approximately closed under policy improvement, with an optimality gap proportional to the inherent Bellman error.
--
--   **Formalization Note** The page states the bound with the effective concentrability coefficient $\kappa_\rho$, the least scalar satisfying (13); it is stated here for every nonnegative $\kappa$ satisfying (13), which gives the page's bound at $\kappa_\rho$ whenever $\kappa_\rho<\infty$ (and the page's bound is vacuous otherwise). The hypothesis $\kappa\ge0$ excludes a degenerate negative coefficient that is not the page's $\kappa_\rho$. Assumptions 1 and 2 and the optimal policy $\pi^*$ are the standing setting of §2. Condition 0 is the joint form; the Bellman operators carry $\gamma$. Condition 1 is not assumed and $\pi^*$ need not lie in $\Pi_\Theta$.
-- source:
--   arXiv:1906.01786v3, Theorem 5, p. 26

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_ApproxClosure_Condition5

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- Theorem 5, p. 26: every stationary point of an approximately closed policy class has cost at most `κε/(1−γ)` above optimal. -/
theorem stationary_gap_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar)
    (hA1 : PGLandscape.Closure.Assumption1 M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (ε κ : ℝ) (hκ : 0 ≤ κ) (hκb : PGLandscape.Closure.IsConcBound M Θ πθ πstar κ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC2 : PGLandscape.Closure.Condition2A M Θ πθ)
    (hC5 : Condition5 M Θ πθ ε) :
    (∀ θ ∈ Θ, ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧ θ ∈ U ∧ ContDiffOn ℝ 1 (PGLandscape.Closure.lossParam M πθ) U) ∧
    ∀ θ, PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ →
      PGLandscape.Closure.loss M (πθ θ) - PGLandscape.Closure.loss M πstar ≤ κ / (1 - M.γ) * ε := by sorry
end PGLandscape.ApproxClosure

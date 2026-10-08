-- Prove2me | Theorems.Thm_PGLandscape_Closure_stationary_iff_optimal
-- name    : PGLandscape.Closure.stationary_iff_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:29:15.53836+00:00
-- url     : https://prove2.me/theorems/97b33cca-9d34-4e3b-8aef-d895514716c0
-- title:
--   Theorem 1, p. 14 — under Conditions 0, 1, 2.A, ℓ is C¹ and θ ∈ Θ is stationary iff ℓ(π_θ) = ℓ(π*)
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process with an optimal policy $\pi^*$, satisfying Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection). Let $\Pi_\Theta = \{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class over a convex set $\Theta\subseteq\mathbb R^d$, and $\ell(\theta) = \ell(\pi_\theta) = (1-\gamma)\int J_{\pi_\theta}\,d\rho$. Suppose
--   1. Condition 0 (differentiability of the weighted policy-iteration objective),
--   2. Condition 1 (closure of $\Pi_\Theta$ under policy improvement), and
--   3. Condition 2.A (for each $\pi\in\Pi_\Theta$, $\bar\theta\mapsto\mathcal B(\bar\theta\mid\eta_\pi,J_\pi)$ has no suboptimal stationary points on $\Theta$)
--
--   hold. Then $\ell$ is continuously differentiable on a neighbourhood of every point of $\Theta$, and for every $\theta\in\Theta$,
--   $$\theta\ \text{is a stationary point of }\ell\text{ on }\Theta\quad\Longleftrightarrow\quad\ell(\pi_\theta) = \ell(\pi^*).$$
--
--   This is the paper's first landscape result: when the policy class is closed under policy improvement and each single-period problem is benign, the nonconvex policy gradient objective has no suboptimal stationary points, and every stationary point is globally optimal among all feasible policies, not only within the class.
--
--   **Formalization Note** A stationary point $\theta$ of $\ell$ on $\Theta$ means: $\ell$ is differentiable at $\theta$ and $\langle\theta'-\theta,\nabla\ell(\theta)\rangle\ge0$ for all $\theta'\in\Theta$. $\ell(\pi^*)$ is the global minimum over all feasible policies, via an optimal policy $\pi^*$; $\Pi_\Theta$ is not assumed to contain it. Condition 0 is the joint form ($C^1$ of $(\bar\theta,\theta')\mapsto\mathcal B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ near $(\theta,\theta)$), which implies the printed condition on the two partial maps and is what the paper's proof of Lemma 6 uses. Assumptions 1 and 2 are standing assumptions of §2. $\mathcal S$, $\mathcal A$ are general measurable spaces, and cost and kernel are defined on all of $\mathcal S\times\mathcal A$. The Bellman operators include the factor $\gamma$ that the printed (3)–(4) omit.
-- source:
--   arXiv:1906.01786v3, Theorem 1, p. 14 (proof pp. 14–15)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem stationary_iff_optimal {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : MDP S A) (πstar : MPolicy S A) (hopt : IsOptimal M πstar)
    (hA1 : Assumption1 M πstar) (hA2 : Assumption2 M) {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A)
    (hΘ : IsPolicyClass M Θ πθ) (hC0 : Condition0 M Θ πθ) (hC1 : Condition1 M Θ πθ)
    (hC2 : Condition2A M Θ πθ) :
    (∀ θ ∈ Θ, ∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ θ ∈ U ∧
        ContDiffOn ℝ 1 (lossParam M πθ) U) ∧
      ∀ θ ∈ Θ, (IsStationary (lossParam M πθ) Θ θ ↔ loss M (πθ θ) = loss M πstar) := by sorry

end PGLandscape.Closure

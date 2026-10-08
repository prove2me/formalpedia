-- Prove2me | Theorems.Thm_PGLandscape_Closure_stationary_bellman_equation
-- name    : PGLandscape.Closure.stationary_bellman_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:24.6811+00:00
-- url     : https://prove2.me/theorems/71b597bf-8f34-42bd-89e2-507c6460d25d
-- title:
--   Lemma 7, p. 14 — at a stationary point θ of ℓ, ∫ J_{π_θ} dη_{π_θ} = min_{π∈Π_Θ} ∫ (T_π J_{π_θ}) dη_{π_θ}
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\Pi_\Theta = \{\pi_\theta:\theta\in\Theta\}$ a parameterized policy class over a convex $\Theta\subseteq\mathbb R^d$, with $\ell(\theta) = \ell(\pi_\theta)$. Suppose Conditions 0 and 2.A hold. If $\theta$ is a stationary point of $\ell$ on $\Theta$, then
--   $$\int J_{\pi_\theta}\,d\eta_{\pi_\theta} = \min_{\pi\in\Pi_\Theta}\int(T_\pi J_{\pi_\theta})\,d\eta_{\pi_\theta},$$
--   and the minimum is attained at $\pi = \pi_\theta$. Explicitly:
--   1. $\int J_{\pi_\theta}\,d\eta_{\pi_\theta} = \int(T_{\pi_\theta}J_{\pi_\theta})\,d\eta_{\pi_\theta}$;
--   2. $\int J_{\pi_\theta}\,d\eta_{\pi_\theta}\le\int(T_{\pi_{\theta'}}J_{\pi_\theta})\,d\eta_{\pi_\theta}$ for every $\theta'\in\Theta$.
--
--   The lemma is a Bellman-type equation at stationary points: no policy in the class improves on $\pi_\theta$ in the single-period problem weighted by its own occupancy measure.
--
--   **Formalization Note** The page's hypothesis lists only Condition 2.A; its proof invokes Lemma 6, which needs Condition 0, so Condition 0 is a hypothesis here. The page's $\min$ over $\Pi_\Theta$ is stated as the two facts above (value attained at $\pi_\theta$ and a lower bound over the class) rather than as a real infimum. Condition 0 is in the joint form of the definition file.
-- source:
--   arXiv:1906.01786v3, Lemma 7, p. 14 (proof p. 15)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem stationary_bellman_equation {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) (hΘ : IsPolicyClass M Θ πθ)
    (hC0 : Condition0 M Θ πθ) (hC2 : Condition2A M Θ πθ) (θ : EuclideanSpace ℝ (Fin d))
    (hstat : IsStationary (lossParam M πθ) Θ θ) :
    ∫ s, costToGo M (πθ θ) s ∂(occupancy M (πθ θ)) = piObjective M πθ θ θ ∧
      ∀ θ' ∈ Θ, ∫ s, costToGo M (πθ θ) s ∂(occupancy M (πθ θ)) ≤ piObjective M πθ θ θ' := by sorry

end PGLandscape.Closure

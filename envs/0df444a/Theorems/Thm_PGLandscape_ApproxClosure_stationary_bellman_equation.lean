-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_stationary_bellman_equation
-- name    : PGLandscape.ApproxClosure.stationary_bellman_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:01.878519+00:00
-- url     : https://prove2.me/theorems/3aa8a167-26cd-4ae4-9359-5db2f7e47bc9
-- title:
--   Lemma 7, p. 14 — at a stationary point, ∫ J_{π_θ} dη_{π_θ} = min_{π∈Π_Θ} ∫ (T_π J_{π_θ}) dη_{π_θ}
-- statement:
--   Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class with $\Theta\subseteq\mathbb R^d$ convex, and assume Conditions 0 and 2.A. If $\theta$ is a stationary point of $\ell(\theta)=\ell(\pi_\theta)$ on $\Theta$, then
--
--   $$
--   \int J_{\pi_\theta}\,d\eta_{\pi_\theta}=\min_{\pi\in\Pi_\Theta}\int (T_\pi J_{\pi_\theta})\,d\eta_{\pi_\theta},
--   $$
--
--   and the minimum is attained at $\pi=\pi_\theta$. Thus a stationary point of the long-run objective is a minimizer, within the class, of the occupancy-weighted one-step policy improvement objective.
--
--   **Formalization Note** The minimum is stated as two facts: $\int J_{\pi_\theta}\,d\eta_{\pi_\theta}=B(\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})$, and $\int J_{\pi_\theta}\,d\eta_{\pi_\theta}\le B(\theta'\mid\eta_{\pi_\theta},J_{\pi_\theta})$ for every $\theta'\in\Theta$. Condition 0 is not in the lemma's sentence; its proof uses Lemma 6, which needs it, so it is added. Condition 0 is the joint form (see the Conditions definition).
-- source:
--   arXiv:1906.01786v3, Lemma 7, p. 14

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- Lemma 7, p. 14: under Condition 2.A (and Condition 0, which its proof uses through Lemma 6), at
a stationary point `θ`, `∫ J_{π_θ} dη_{π_θ} = min_{π∈Π_Θ} ∫ (T_π J_{π_θ}) dη_{π_θ}`, the minimum
being attained at `π_θ` itself. -/
theorem stationary_bellman_equation {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC2 : PGLandscape.Closure.Condition2A M Θ πθ) (θ : EuclideanSpace ℝ (Fin d))
    (hstat : PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ) :
    ∫ s, PGLandscape.Closure.costToGo M (πθ θ) s ∂(PGLandscape.Closure.occupancy M (πθ θ)) = PGLandscape.Closure.piObjective M πθ θ θ ∧
      ∀ θ' ∈ Θ, ∫ s, PGLandscape.Closure.costToGo M (πθ θ) s ∂(PGLandscape.Closure.occupancy M (πθ θ)) ≤ PGLandscape.Closure.piObjective M πθ θ θ' := by sorry

end PGLandscape.ApproxClosure

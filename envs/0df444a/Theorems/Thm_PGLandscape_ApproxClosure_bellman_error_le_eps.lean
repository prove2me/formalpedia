-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_bellman_error_le_eps
-- name    : PGLandscape.ApproxClosure.bellman_error_le_eps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:09.21098+00:00
-- url     : https://prove2.me/theorems/0092113b-e6e8-4086-b1a4-567c5b4dd14f
-- title:
--   §8, proof of Theorem 5, first display, p. 26 — at a stationary point, ‖J_{π_θ} − TJ_{π_θ}‖_{1,η_{π_θ}} ≤ ϵ
-- statement:
--   Assume the standing setting of §2 (an optimal policy $\pi^*$, Assumptions 1 and 2), a parameterized policy class $\Pi_\Theta$, Conditions 0 and 2.A, and Condition 5 with inherent Bellman error $\varepsilon$. If $\theta$ is a stationary point of $\ell(\theta)=\ell(\pi_\theta)$ on $\Theta$, then the Bellman error of $J_{\pi_\theta}$, weighted by the occupancy measure of $\pi_\theta$, is at most $\varepsilon$:
--
--   $$
--   \|J_{\pi_\theta}-TJ_{\pi_\theta}\|_{1,\eta_{\pi_\theta}}=\int\bigl|J_{\pi_\theta}-TJ_{\pi_\theta}\bigr|\,d\eta_{\pi_\theta}\le\varepsilon .
--   $$
--
--   This is the first display of the proof of Theorem 5: the approximation error of the class bounds the Bellman error at any stationary point.
--
--   **Formalization Note** $T$ carries the discount $\gamma$. Condition 0 is the joint form and enters through Lemma 7. Assumption 2 makes $TJ_{\pi_\theta}$ measurable, so the integral is meaningful.
-- source:
--   arXiv:1906.01786v3, §8, proof of Theorem 5, first display, p. 26

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_ApproxClosure_Condition5

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- The last member of the first display in the proof of Theorem 5, p. 26. -/
theorem bellman_error_le_eps {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar)
    (hA1 : PGLandscape.Closure.Assumption1 M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (ε : ℝ) (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC2 : PGLandscape.Closure.Condition2A M Θ πθ)
    (hC5 : Condition5 M Θ πθ ε)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ) :
    ∫ s, |PGLandscape.Closure.costToGo M (πθ θ) s - PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s|
      ∂(PGLandscape.Closure.occupancy M (πθ θ)) ≤ ε := by sorry
end PGLandscape.ApproxClosure

-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_policy_gradient_theorem
-- name    : PGLandscape.ApproxClosure.policy_gradient_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:43.207572+00:00
-- url     : https://prove2.me/theorems/6b099e20-3472-41c3-a651-ffe016b1b851
-- title:
--   Lemma 6, p. 13 — policy gradient theorem: ℓ is C¹ and ∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ}) at θ̄ = θ
-- statement:
--   Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class and assume Condition 0. For every $\theta\in\Theta$, the objective $\ell(\theta)=\ell(\pi_\theta)$ is continuously differentiable on a neighbourhood of $\theta$, and
--
--   $$
--   \nabla\ell(\theta)=\nabla_{\bar\theta}\,B(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})\Big|_{\bar\theta=\theta},
--   $$
--
--   where $B(\bar\theta\mid\eta,J)=\int (T_{\pi_{\bar\theta}}J)\,d\eta$ is the weighted policy-iteration objective. The gradient of the long-run cost is thus the gradient of a single-period objective.
--
--   **Formalization Note** Condition 0 is used in the joint form: $(\bar\theta,\theta')\mapsto B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ is $C^1$ near $(\theta,\theta)$. The page (p. 13) asks only for its two partial maps to be $C^1$; its proof (p. 39) expands the total derivative into partial derivatives, which needs the joint form.
-- source:
--   arXiv:1906.01786v3, Lemma 6, pp. 13, 39

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (Policy gradient theorem), p. 13: under Condition 0, `ℓ` is continuously
differentiable near `θ` and `∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ})` at `θ̄ = θ`. -/
theorem policy_gradient_theorem {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    (∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ θ ∈ U ∧ ContDiffOn ℝ 1 (PGLandscape.Closure.lossParam M πθ) U) ∧
      gradient (PGLandscape.Closure.lossParam M πθ) θ = gradient (PGLandscape.Closure.piObjective M πθ θ) θ := by sorry

end PGLandscape.ApproxClosure

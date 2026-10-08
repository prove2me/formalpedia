-- Prove2me | Theorems.Thm_PGLandscape_GradDom_policy_gradient_theorem
-- name    : PGLandscape.GradDom.policy_gradient_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:54.131081+00:00
-- url     : https://prove2.me/theorems/337ce39a-9b83-48d0-89bc-57741981ccd4
-- title:
--   Lemma 6, p. 13 — policy gradient theorem: under Condition 0, ℓ is C¹ and ∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ}) at θ̄ = θ
-- statement:
--   Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class with convex $\Theta\subseteq\mathbb R^d$, let $\ell(\theta)=\ell(\pi_\theta)$, and suppose Condition 0 holds. Then for every $\theta\in\Theta$, $\ell$ is continuously differentiable on an open neighbourhood of $\theta$, and
--   $$\nabla\ell(\theta)=\nabla_{\bar\theta}\,\mathcal B(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})\Big|_{\bar\theta=\theta}.$$
--
--   The gradient of the multi-period objective equals the gradient of the single-period weighted policy iteration objective of the current policy. This is how Theorem 2 transfers gradient dominance from $\mathcal B$ to $\ell$.
--
--   **Formalization Note** "$\ell$ is continuously differentiable" is stated locally: around each $\theta\in\Theta$ there is an open set on which $\ell$ is $C^1$. $\nabla$ is the Euclidean gradient. Condition 0 is used in the joint form that the proof of Lemma 6 (p. 39) needs: $(\bar\theta,\theta')\mapsto \mathcal B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ is continuously differentiable on an open set containing $(\theta,\theta)$. Its two partial maps at $(\theta,\theta)$ are the two functions of the printed Condition 0, so it implies the printed condition; the printed condition alone does not give the total-derivative expansion of that proof.
-- source:
--   arXiv:1906.01786v3, Lemma 6, p. 13 (restated with proof, p. 39)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (Policy gradient theorem), p. 13: under Condition 0, `ℓ` is continuously differentiable
on an open set around every `θ ∈ Θ`, and `∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ})` at `θ̄ = θ`. -/
theorem policy_gradient_theorem {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ) (hC0 : PGLandscape.Closure.Condition0 M Θ πθ)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    (∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ θ ∈ U ∧ ContDiffOn ℝ 1 (PGLandscape.Closure.lossParam M πθ) U) ∧
      gradient (PGLandscape.Closure.lossParam M πθ) θ = gradient (PGLandscape.Closure.piObjective M πθ θ) θ := by sorry

end PGLandscape.GradDom

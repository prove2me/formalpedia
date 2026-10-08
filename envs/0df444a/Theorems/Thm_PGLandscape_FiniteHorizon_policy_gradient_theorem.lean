-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_policy_gradient_theorem
-- name    : PGLandscape.FiniteHorizon.policy_gradient_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:08.149084+00:00
-- url     : https://prove2.me/theorems/4d00c8cc-3d38-42d6-a618-0225946e661b
-- title:
--   Lemma 6, p. 13 — under Condition 0, ℓ is C¹ and ∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ}) at θ̄ = θ
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process, $\Theta\subseteq\mathbb R^d$ convex and $\theta\mapsto\pi_\theta$ a parameterization by measurable policies with $\pi_\theta\in\Pi$ for $\theta\in\Theta$. Write $\ell(\theta) = \ell(\pi_\theta)$ and $\mathcal B(\bar\theta\mid\eta,J) = \int(T_{\pi_{\bar\theta}}J)\,d\eta$. Suppose Condition 0 holds. Then for every $\theta\in\Theta$:
--   1. $\ell$ is continuously differentiable on an open set containing $\theta$;
--   2. the gradient of $\ell$ at $\theta$ is the gradient of the single-period objective of $\pi_\theta$:
--   $$\nabla\ell(\theta) = \nabla_{\bar\theta}\,\mathcal B(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})\Big|_{\bar\theta=\theta}.$$
--
--   This is the paper's policy gradient theorem, valid for deterministic policies on general state spaces. It identifies a gradient step on $\ell$ with a gradient step on the policy-iteration objective, which is how the landscape of $\ell$ inherits properties of the single-period problems.
--
--   **Formalization Note** Condition 0 is the joint form: for each $\theta\in\Theta$, $(\bar\theta,\theta')\mapsto\mathcal B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ is $C^1$ on an open set containing $(\theta,\theta)$. The printed Condition 0 asks only for its two partial maps; the paper's proof (p. 39) expands a total derivative into partials, which needs the joint form, and the joint form implies the printed one. "Continuously differentiable" is formalized as $C^1$ on an open neighbourhood of each point of $\Theta$, the domain on which Condition 0 is assumed. Gradients are taken in $\mathbb R^d$ with the Euclidean inner product.
-- source:
--   arXiv:1906.01786v3, Lemma 6, p. 13 (restated with proof p. 39)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (policy gradient theorem), arXiv:1906.01786v3, p. 13 (proof p. 39): under Condition 0,
`ℓ(θ)` is continuously differentiable (on an open set around `θ ∈ Θ`) and
`∇ℓ(θ) = ∇_θ̄ B(θ̄ | η_{π_θ}, J_{π_θ})|_{θ̄ = θ}`. -/
theorem policy_gradient_theorem {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    (∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ θ ∈ U ∧
        ContDiffOn ℝ 1 (PGLandscape.Closure.lossParam M πθ) U) ∧
      gradient (PGLandscape.Closure.lossParam M πθ) θ = gradient (PGLandscape.Closure.piObjective M πθ θ) θ := by sorry

end PGLandscape.FiniteHorizon

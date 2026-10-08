-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_value_smoothness
-- name    : PolicyGradTheory.Softmax.softmax_value_smoothness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:49:43.180361+00:00
-- url     : https://prove2.me/theorems/56f3e877-acd9-4f1a-a8b1-9700e2513803
-- title:
--   Lemma D.4 at λ = 0, p. 75 — θ ↦ V^{π_θ}(µ) is β-smooth with β = 8/(1−γ)³ under softmax
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, with $\mathcal A$ nonempty, and let $\mu$ be a probability distribution on $\mathcal S$. For the softmax parameterization $\pi_\theta$, the objective $\theta\mapsto V^{\pi_\theta}(\mu)$ has a Lipschitz gradient: for all $\theta,\theta'\in\mathbb R^{|\mathcal S||\mathcal A|}$,
--   $$
--   \|\nabla_\theta V^{\pi_\theta}(\mu)-\nabla_\theta V^{\pi_{\theta'}}(\mu)\|_2\le\frac{8}{(1-\gamma)^3}\,\|\theta-\theta'\|_2 .
--   $$
--
--   This is the case $\lambda=0$ of Lemma D.4, which states $\beta_\lambda=8/(1-\gamma)^3+2\lambda/|\mathcal S|$ for the log-barrier regularized objective $L_\lambda$; the proof of Lemma C.5 invokes Lemma D.4 exactly for the smoothness of $V^{\pi_\theta}(\mu)$. Smoothness is what lets the standard gradient ascent analysis conclude that the gradients along a run vanish.
--
--   **Formalization Note** Norms are Euclidean on $\mathbb R^{\mathcal S\times\mathcal A}$ and $\nabla_\theta$ is Mathlib's `gradient`.
-- source:
--   arXiv:1908.00261v5, Lemma D.4 (case λ = 0), p. 75; used in the proof of Lemma C.5, p. 63

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma D.4 (arXiv:1908.00261v5, p. 75) at `λ = 0`, the case used in the proof of Lemma C.5
(p. 63): for the softmax parameterization, `θ ↦ V^{π_θ}(µ)` is `β`-smooth with
`β = 8/(1−γ)³`. -/
theorem softmax_value_smoothness {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (θ θ' : EuclideanSpace ℝ (S × A)) :
    ‖gradient (softmaxValue P r γ μ) θ - gradient (softmaxValue P r γ μ) θ'‖ ≤
      8 / (1 - γ) ^ 3 * ‖θ - θ'‖ := by sorry

end PolicyGradTheory.Softmax

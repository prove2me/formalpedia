-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_grad_stateValue_unrolled
-- name    : SuttonBartoRL.PolicyGradient.grad_stateValue_unrolled
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:31.231256+00:00
-- url     : https://prove2.me/theorems/fd36772d-ca9e-4894-95ec-fa036083e606
-- title:
--   The unrolled gradient $\nabla v_\pi(s) = \sum_x \sum_k \Pr(s \to x, k, \pi) \sum_a \nabla\pi(a\mid x) q_\pi(x,a)$
-- statement:
--   Let a finite episodic MDP and a differentiable policy parameterization be given, and let episodes terminate under $\pi_{\theta_0}$. Then for every nonterminal state $s$ the map $\theta \mapsto v_{\pi_\theta}(s)$ is differentiable at $\theta_0$ and
--   $$
--   \nabla v_\pi(s) = \sum_{x \in \mathcal S} \sum_{k=0}^{\infty} \Pr(s \to x, k, \pi) \sum_a \nabla \pi(a\mid x)\, q_\pi(x, a),
--   $$
--   where $\Pr(s \to x, k, \pi)$ is the probability of transitioning from $s$ to $x$ in $k$ steps under $\pi = \pi_{\theta_0}$ and all gradients are taken at $\theta_0$.
--
--   This is the identity "after repeated unrolling" in the proof box; the policy gradient theorem is its case $s = s_0$.
--
--   **Formalization Note** $\Pr(s \to x, k, \pi)$ is the $(s,x)$ entry of $P_{\theta_0}^k$. The result is stated for every start state, not only $s_0$, as in the book.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of the Policy Gradient Theorem (episodic case)", p. 325

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- Box "Proof of the Policy Gradient Theorem (episodic case)", p. 325, "after repeated unrolling":
if episodes terminate under `π_{θ₀}`, then for every state `s`
`∇v_π(s) = Σ_{x ∈ S} Σ_{k=0}^{∞} Pr(s → x, k, π) Σ_a ∇π(a|x) q_π(x, a)`, where
`Pr(s → x, k, π) = (P_θ^k)(s, x)`. -/
theorem grad_stateValue_unrolled {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) (s : S) :
    HasGradientAt (fun θ => M.stateValue π θ s)
      (∑ x, (∑' k : ℕ, (M.policyTrans π θ₀ ^ k) s x) •
        ∑ a, M.actionValue π θ₀ x a • gradient (fun θ => π.prob θ x a) θ₀)
      θ₀ := by sorry

end SuttonBartoRL.PolicyGradient

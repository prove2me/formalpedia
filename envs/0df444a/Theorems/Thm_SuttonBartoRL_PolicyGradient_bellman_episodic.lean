-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_bellman_episodic
-- name    : SuttonBartoRL.PolicyGradient.bellman_episodic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:39:26.672866+00:00
-- url     : https://prove2.me/theorems/199faade-158c-4177-9cda-3829e0dbbd6c
-- title:
--   Exercises 3.18–3.19 in the episodic case $\gamma = 1$
-- statement:
--   Let a finite episodic MDP and a differentiable policy parameterization be given, and fix $\theta$ such that episodes terminate under $\pi_\theta$. Write $\pi(a\mid s) = \pi(a \mid s,\theta)$ and let $v_\pi$, $q_\pi$ be the return-defined state and action values with $\gamma = 1$, extended by $v_\pi(\text{terminal}) = 0$. Then for every nonterminal state $s$ and action $a$
--   $$
--   v_\pi(s) = \sum_a \pi(a\mid s)\, q_\pi(s,a), \qquad
--   q_\pi(s,a) = \sum_{s' \in \mathcal S^+}\sum_{r} p(s', r \mid s, a)\,\big(r + v_\pi(s')\big).
--   $$
--
--   These are the two identities (Exercise 3.18, Exercise 3.19 with Equation 3.2) with which the proof of the policy gradient theorem opens.
--
--   **Formalization Note** Termination is the book's implicit assumption for $\gamma = 1$; without it the values are infinite series that need not converge.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercises 3.18–3.19, p. 62, as used in the box "Proof of the Policy Gradient Theorem (episodic case)", p. 325

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- Exercises 3.18 and 3.19 (p. 62) as used in the box "Proof of the Policy Gradient Theorem
(episodic case)", p. 325, with `γ = 1`: if episodes terminate under `π_θ`, the return-defined values
satisfy `v_π(s) = Σ_a π(a|s) q_π(s, a)` and `q_π(s, a) = Σ_{s', r} p(s', r|s, a)(r + v_π(s'))`, with
`v_π = 0` at the terminal state. -/
theorem bellman_episodic {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) :
    (∀ s, M.stateValue π θ s = ∑ a, π.prob θ s a * M.actionValue π θ s a) ∧
    (∀ s a, M.actionValue π θ s a =
      ∑ s' : Option S, ∑ r ∈ M.R,
        M.p s a s' r * (r + EpisodicMDP.valuePlus (M.stateValue π θ) s')) := by sorry

end SuttonBartoRL.PolicyGradient

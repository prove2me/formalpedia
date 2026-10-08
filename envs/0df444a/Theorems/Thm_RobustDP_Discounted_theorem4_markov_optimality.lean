-- Prove2me | Theorems.Thm_RobustDP_Discounted_theorem4_markov_optimality
-- name    : RobustDP.Discounted.theorem4_markov_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:49:21.064985+00:00
-- url     : https://prove2.me/theorems/f497e814-7467-4977-a283-bcaa7d7c51fd
-- title:
--   Theorem 4 (Markov optimality) — V*_λ(s) = sup over deterministic Markov policies of V^π_λ(s)
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP. For every state $s$,
--   $$V^*_\lambda(s)=\sup_{\pi\in\Pi}V^\pi_\lambda(s)=\sup_{\pi\in\Pi_{MD}}V^\pi_\lambda(s),$$
--   where $\Pi$ is the set of all history dependent randomized policies and $\Pi_{MD}$ the set of deterministic Markov policies.
--
--   The decision maker loses nothing by restricting to deterministic Markov policies, even though the adversary is history dependent.
--
--   **Formalization Note** $\Pi_{MD}$ is parametrized by sequences $(d_0,d_1,\dots)$ of deterministic Markov decision rules. The page gives only a proof by citation (robust extensions of Theorems 5.5.1, 5.5.3 and Proposition 6.2.1 of Puterman 1994).
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 9, Theorem 4

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem theorem4_markov_optimality {S A : Type*} [Countable S] [Countable A]
    (M : Model S A) (s : S) :
    Vstar M s = ⨆ f : ℕ → DecisionRule M, V M (markovPolicy M f) s := by sorry

end RobustDP.Discounted

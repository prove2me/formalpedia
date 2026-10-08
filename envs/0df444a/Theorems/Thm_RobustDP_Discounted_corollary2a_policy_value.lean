-- Prove2me | Theorems.Thm_RobustDP_Discounted_corollary2a_policy_value
-- name    : RobustDP.Discounted.corollary2a_policy_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:03.692481+00:00
-- url     : https://prove2.me/theorems/1832667d-f825-4f1d-b4b0-16fc8b465a8a
-- title:
--   Corollary 2(a) — the robust value of a stationary policy (d, d, …) is the unique bounded solution of (29)
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP, let $d$ be a deterministic Markov decision rule, and let $\pi=(d,d,\dots)$. Then $V^\pi_\lambda$ is bounded, it solves
--   $$V(s)=\inf_{p\in\mathcal P(s,d(s))}\mathbf E^p\big[r(s,d(s),s')+\lambda V(s')\big],\qquad s\in\mathcal S,\tag{29}$$
--   and every bounded solution of (29) equals $V^\pi_\lambda$.
--
--   This is robust policy evaluation: it is the base of Lemmas 2 and 3 and of the robust policy iteration algorithm.
--
--   **Formalization Note** "Deterministic decision rule" is a deterministic Markov rule $d:\mathcal S\to\mathcal A$, as throughout Section 3. Uniqueness is among bounded functions. $V^\pi_\lambda$ is the robust value against the dynamic adversary.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 11, Corollary 2(a), eq. (29)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem corollary2a_policy_value {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (d : DecisionRule M) :
    IsBounded (V M (stationary M d)) ∧
      (∀ s, V M (stationary M d) s = Q M (V M (stationary M d)) s (d.1 s)) ∧
      ∀ U : S → ℝ, IsBounded U → (∀ s, U s = Q M U s (d.1 s)) → U = V M (stationary M d) := by sorry

end RobustDP.Discounted

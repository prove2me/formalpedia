-- Prove2me | Theorems.Thm_RobustDP_Discounted_corollary2b_value_unique_fixed_point
-- name    : RobustDP.Discounted.corollary2b_value_unique_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:36.757749+00:00
-- url     : https://prove2.me/theorems/d97ce751-439b-44b3-aff9-ab28cb79ea55
-- title:
--   Corollary 2(b) — V*_λ is the unique bounded solution of the robust optimality equation (30), and ε-optimal stationary policies exist
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP with robust value function $V^*_\lambda(s)=\sup_{\pi\in\Pi}V^\pi_\lambda(s)$, the supremum over all history dependent randomized policies. Then
--
--   1. $V^*_\lambda$ is bounded and solves
--   $$V(s)=\sup_{a\in\mathcal A(s)}\ \inf_{p\in\mathcal P(s,a)}\mathbf E^p\big[r(s,a,s')+\lambda V(s')\big],\qquad s\in\mathcal S;\tag{30}$$
--   2. every bounded solution of (30) equals $V^*_\lambda$;
--   3. for every $\epsilon>0$ there is a deterministic Markov decision rule $d^\epsilon$ whose stationary policy $\pi^\epsilon=(d^\epsilon,d^\epsilon,\dots)$ satisfies $V^{\pi^\epsilon}_\lambda(s)\ge V^*_\lambda(s)-\epsilon$ for every $s$.
--
--   This is the robust Bellman equation of discounted dynamic programming: the robust value function is computed by a fixed point of a state-wise max–min operator, and nearly optimal policies can be taken stationary.
--
--   **Formalization Note** "Unique solution" is uniqueness among bounded functions (the space $\mathbf V$ of the page). The $\epsilon$-optimal stationary policy is deterministic, as the page's construction (28) gives. $V^\pi_\lambda$ is the value against the dynamic (rectangular) adversary.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 11, Corollary 2(b), eq. (30)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem corollary2b_value_unique_fixed_point {S A : Type*} [Countable S] [Countable A]
    (M : Model S A) :
    IsBounded (Vstar M) ∧ (∀ s, Vstar M s = T M (Vstar M) s) ∧
      (∀ U : S → ℝ, IsBounded U → (∀ s, U s = T M U s) → U = Vstar M) ∧
      ∀ ε : ℝ, 0 < ε → ∃ d : DecisionRule M, ∀ s, Vstar M s - ε ≤ V M (stationary M d) s := by sorry

end RobustDP.Discounted

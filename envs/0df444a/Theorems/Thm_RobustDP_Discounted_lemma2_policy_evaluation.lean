-- Prove2me | Theorems.Thm_RobustDP_Discounted_lemma2_policy_evaluation
-- name    : RobustDP.Discounted.lemma2_policy_evaluation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:34.550273+00:00
-- url     : https://prove2.me/theorems/d6803d72-4cb2-42d3-a180-9d74d3e78ece
-- title:
--   Lemma 2 (Policy evaluation) — V^π of a stationary policy is the optimal solution of the robust program (31)
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP, let $d$ be a deterministic Markov decision rule, $\pi=(d,d,\dots)$, and let $\alpha:\mathcal S\to\mathbb R$ with $\alpha(s)>0$ for all $s$ and $\sum_s\alpha(s)<\infty$. Consider the robust program
--   $$\text{maximize}\ \sum_{s\in\mathcal S}\alpha(s)V(s)\quad\text{subject to}\quad V(s)\le\mathbf E^p[r_s+\lambda V]\ \ \forall p\in\mathcal P(s,d(s)),\ s\in\mathcal S,\tag{31}$$
--   over bounded $V:\mathcal S\to\mathbb R$, where $r_s(s')=r(s,d(s),s')$. Then
--
--   1. $V^\pi_\lambda$ is feasible for (31);
--   2. every feasible $V$ has $\sum_s\alpha(s)V(s)\le\sum_s\alpha(s)V^\pi_\lambda(s)$;
--   3. every feasible $V$ attaining $\sum_s\alpha(s)V(s)=\sum_s\alpha(s)V^\pi_\lambda(s)$ equals $V^\pi_\lambda$.
--
--   So robust policy evaluation is a (convex) robust optimization problem, the first step of robust policy iteration.
--
--   **Formalization Note** With a countable state space the objective needs $\sum_s\alpha(s)<\infty$ and bounded $V$; both are added and restrict the page's program to bounded $V$. "The optimal solution" is rendered as feasibility, optimality and uniqueness of the maximizer.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 12, Lemma 2, eq. (31)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem lemma2_policy_evaluation {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (d : DecisionRule M) (α : S → ℝ) (hα : ∀ s, 0 < α s) (hαs : Summable α) :
    let feasible : (S → ℝ) → Prop := fun U =>
      IsBounded U ∧ ∀ s, ∀ p ∈ M.P s (d.1 s),
        U s ≤ RobustDP.FiniteHorizon.expect p (fun s' => M.r s (d.1 s) s' + M.lam * U s')
    feasible (V M (stationary M d)) ∧
      (∀ U, feasible U → ∑' s, α s * U s ≤ ∑' s, α s * V M (stationary M d) s) ∧
      ∀ U, feasible U → ∑' s, α s * U s = ∑' s, α s * V M (stationary M d) s →
        U = V M (stationary M d) := by sorry

end RobustDP.Discounted

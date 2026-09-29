-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_dual_feasible_of_no_potential_move
-- name    : RestrictedAssignment.Svensson.dual_feasible_of_no_potential_move
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:28:33.665466+00:00
-- url     : https://prove2.me/theorems/63c72c85-5882-4ecc-acca-9c9a49af913e
-- title:
--   Claim 4.7 — with no potential move, $(y^*, z^*)$ is dual feasible
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment with $p_j \ge 0$ for all $j$, let $\sigma_0$ be a valid partial schedule and $j_{\mathrm{new}}$ a job with $\sigma_0(j_{\mathrm{new}}) = \mathrm{TBD}$. Let $(\sigma, T)$ be a state reached by Algorithm 2 on $(\sigma_0, j_{\mathrm{new}})$ in which $\sigma(j_{\mathrm{new}})$ is still TBD and no potential move is available. Then the pair $(y^*, z^*)$ defined from $(\sigma, T)$ is a feasible solution of the dual of [C-LP] for target makespan $1$:
--   $$
--   y^*, z^* \ge 0, \qquad y^*_i \ \ge\ \sum_{j \in C} z^*_j \quad \text{for all } i \in M,\ C \in \mathcal C(i, 1).
--   $$
--
--   Together with Claim 4.8 this shows that when Algorithm 2 is stuck, [C-LP] is infeasible.
--
--   **Formalization Note** The state ranges over states reachable from the initial state, as in the paper, where the proof uses how each blocker was added.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 15, Claim 4.7

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 15, Claim 4.7: in an iteration of Algorithm 2 in which no
potential move is available, `(y*, z*)` is a feasible solution of the dual of [C-LP]
(target makespan 1). -/
theorem dual_feasible_of_no_potential_move {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (s : AlgState J M)
    (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none)
    (hnone : ∀ j i, ¬ IsPotentialMove Γ p s j i) :
    CLPDualFeasible Γ p 1 (yStar Γ p s) (zStar Γ p s) := by sorry

end RestrictedAssignment.Svensson

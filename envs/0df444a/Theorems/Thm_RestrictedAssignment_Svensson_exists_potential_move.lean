-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_exists_potential_move
-- name    : RestrictedAssignment.Svensson.exists_potential_move
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:29:49.627488+00:00
-- url     : https://prove2.me/theorems/2d3128fb-1b8c-4e8a-8ff2-99bef5c81a68
-- title:
--   Lemma 4.6 — if [C-LP] is feasible, Algorithm 2 can always pick a potential move
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment with $p_j \ge 0$ for all $j$ such that [C-LP] is feasible for target makespan $1$. Let $\sigma_0$ be a valid partial schedule and $j_{\mathrm{new}}$ a job with $\sigma_0(j_{\mathrm{new}}) = \mathrm{TBD}$. Then in every state $(\sigma, T)$ reached by Algorithm 2 on $(\sigma_0, j_{\mathrm{new}})$ in which $\sigma(j_{\mathrm{new}})$ is still TBD, there is a potential move $(j, i)$.
--
--   This is one of the two halves of the correctness of Algorithm 2: the procedure never gets stuck. The other half is termination (Lemma 4.9).
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 15, Lemma 4.6

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 15, Lemma 4.6: if [C-LP] is feasible (target makespan 1),
then in every iteration of Algorithm 2 there is a potential move to pick. -/
theorem exists_potential_move {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hLP : CLPFeasible Γ p 1)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none) :
    ∃ j i, IsPotentialMove Γ p s j i := by sorry

end RestrictedAssignment.Svensson

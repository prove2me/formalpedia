-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_valid_of_reachable
-- name    : RestrictedAssignment.Svensson.valid_of_reachable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:28:06.417391+00:00
-- url     : https://prove2.me/theorems/b7775c56-eced-4c68-9e42-de99b3c1d16e
-- title:
--   Sect. 4.1 — Algorithm 2 keeps the partial schedule valid
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment, $\sigma_0$ a valid partial schedule (every assigned job on a machine of $\Gamma(j)$, at most one big job per machine, every load at most $1 + R = 33/17$), and $j_{\mathrm{new}}$ a job with $\sigma_0(j_{\mathrm{new}}) = \mathrm{TBD}$. Then every state $(\sigma, T)$ that Algorithm 2 started on $(\sigma_0, j_{\mathrm{new}})$ reaches after finitely many iterations has a valid partial schedule $\sigma$.
--
--   This is the invariant that makes the output of Algorithm 2 a schedule of makespan at most $1 + R$.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 14, Sect. 4.1

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 14, Sect. 4.1: Algorithm 2 only updates the schedule when a
valid move is chosen, so the schedule stays valid throughout the execution. -/
theorem valid_of_reachable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (s : AlgState J M)
    (hs : Reachable Γ p σ0 jnew s) :
    Valid Γ p s.σ := by sorry

end RestrictedAssignment.Svensson

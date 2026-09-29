-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_makespan_le_of_clp_feasible_one
-- name    : RestrictedAssignment.Svensson.makespan_le_of_clp_feasible_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:30:51.895032+00:00
-- url     : https://prove2.me/theorems/2eb79309-bd0c-4554-9ef9-3228dd9306a7
-- title:
--   Sect. 4.1 — if [C-LP] is feasible for $T = 1$, some schedule has makespan at most $1 + R = 33/17$
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment with $p_j \ge 0$ for all $j$. If [C-LP] is feasible for target makespan $1$, then there is a schedule $\sigma : J \to M$ with $\sigma(j) \in \Gamma(j)$ for every job $j$ and
--   $$
--   \sum_{j :\, \sigma(j) = i} p_j \;\le\; 1 + \tfrac{16}{17} \qquad \text{for every machine } i .
--   $$
--
--   This is Theorem 4.1 under the paper's normalization $\mathrm{OPT}_{LP} = 1$; the paper obtains it by calling Algorithm 2 repeatedly, starting from the empty partial schedule, until all jobs are assigned.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 15, Sect. 4.1

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 15, Sect. 4.1: under the normalization `OPT_LP = 1`, if
[C-LP] is feasible for target makespan 1 then there is a schedule respecting `Γ` with makespan
at most `1 + R = 1 + 16/17`. -/
theorem makespan_le_of_clp_feasible_one {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hLP : CLPFeasible Γ p 1) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧ ∀ i, schedLoad p σ i ≤ 1 + 16 / 17 := by sorry

end RestrictedAssignment.Svensson

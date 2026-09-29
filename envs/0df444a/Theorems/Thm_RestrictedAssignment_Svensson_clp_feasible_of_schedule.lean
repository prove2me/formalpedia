-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_clp_feasible_of_schedule
-- name    : RestrictedAssignment.Svensson.clp_feasible_of_schedule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:31:48.12043+00:00
-- url     : https://prove2.me/theorems/450345ac-1f05-47e5-a9cf-3b641c8fd490
-- title:
--   Sect. 2 — a schedule of makespan $T$ makes [C-LP] feasible for $T$ ($\mathrm{OPT}_{LP} \le \mathrm{OPT}$)
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment and $T \in \mathbb R$. If $\sigma : J \to M$ is a schedule with $\sigma(j) \in \Gamma(j)$ for every job and
--   $$
--   \sum_{j :\, \sigma(j) = i} p_j \le T \qquad \text{for every machine } i,
--   $$
--   then [C-LP] is feasible for target makespan $T$.
--
--   Applied to an optimal schedule, this gives $\mathrm{OPT}_{LP} \le \mathrm{OPT}$: [C-LP] is a relaxation, so the bound of Theorem 4.1 is a bound on its integrality gap.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 3, Sect. 2

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: a schedule respecting `Γ` of makespan at most
`T` defines a feasible solution of [C-LP] with target makespan `T`; hence `OPT_LP ≤ OPT`. -/
theorem clp_feasible_of_schedule {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (σ : J → M) (hσ : ∀ j, σ j ∈ Γ j)
    (hload : ∀ i, schedLoad p σ i ≤ T) :
    CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson

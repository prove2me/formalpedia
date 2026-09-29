-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_clp_feasible_scale
-- name    : RestrictedAssignment.Svensson.clp_feasible_scale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:31:17.621564+00:00
-- url     : https://prove2.me/theorems/2215a410-8a4e-44ce-b836-2f23022c63af
-- title:
--   Sect. 2 — scaling processing times normalizes the target makespan to 1
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment and $T > 0$. Then [C-LP] is feasible for target makespan $T$ if and only if [C-LP] for the scaled sizes $p_j / T$ is feasible for target makespan $1$.
--
--   This is the reduction behind the paper's convention $\mathrm{OPT}_{LP} = 1$, which lets every statement of Section 4 be made at $T = 1$.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 3, Sect. 2

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: scaling the processing times by `1/T` turns
[C-LP] for target makespan `T > 0` into [C-LP] for target makespan 1. -/
theorem clp_feasible_scale {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (hT : 0 < T) :
    CLPFeasible Γ p T ↔ CLPFeasible Γ (fun j => p j / T) 1 := by sorry

end RestrictedAssignment.Svensson

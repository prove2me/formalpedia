-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_clp_feasible_mono
-- name    : RestrictedAssignment.Svensson.clp_feasible_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:32:08.931894+00:00
-- url     : https://prove2.me/theorems/65d22719-bc77-4cfb-b4fb-c677ad05b6ad
-- title:
--   Sect. 2 — feasibility of [C-LP] is monotone in the target makespan
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment and $T_0 \le T$. If [C-LP] is feasible for target makespan $T_0$, then it is feasible for target makespan $T$.
--
--   Monotonicity is what makes $\mathrm{OPT}_{LP}$, the least feasible target makespan, a threshold: [C-LP] is feasible exactly at the targets $T \ge \mathrm{OPT}_{LP}$.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 3, Sect. 2

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: if [C-LP] is feasible for target makespan `T₀`
then it is feasible for every `T ≥ T₀`. -/
theorem clp_feasible_mono {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T0 T : ℝ) (hT : T0 ≤ T) (h : CLPFeasible Γ p T0) :
    CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson

-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_yes_instance_lp_feasible
-- name    : UnrelatedSched.TwoApprox.yes_instance_lp_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:17:10.07398+00:00
-- url     : https://prove2.me/theorems/1bde3fd7-d9f2-4dbb-b30e-7bd5438e5385
-- title:
--   §3, p. 5 — a schedule with makespan at most d is a feasible solution of (LP) with d_i = t = d
-- statement:
--   Let $P=(p_{ij})\in\mathbb N^{m\times n}$ and $d\in\mathbb R$, and let $\sigma$ be a schedule with makespan at most $d$. Then its 0-1 matrix, $x_{ij}=1$ if job $j$ is assigned to machine $i$ and $0$ otherwise, is a feasible solution of the linear program (LP) with
--   $$d_1=\dots=d_m=t=d .$$
--
--   This is the 'yes' direction of the 2-relaxed decision procedure: if (LP) has no feasible point, no schedule meets the deadline $d$.
--
--   **Formalization Note** Feasibility includes $x_{ij}=0$ whenever $p_{ij}>d$, which holds because each processing time of an assigned job is at most its machine's load.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 5, §3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- §3, p. 5: the 0-1 matrix of a schedule with makespan at most `d` is feasible for (LP) with
`d_1 = ⋯ = d_m = t = d`. -/
theorem yes_instance_lp_feasible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : ℝ)
    (σ : Fin n → Fin m) (hσ : makespan (realTimes P) σ ≤ d) :
    assignmentMatrix σ ∈ LPPolytope P (fun _ => d) d := by sorry

end UnrelatedSched.TwoApprox

-- Prove2me | Theorems.Thm_UnrelatedSched_FixedMachines_residual_lp_feasible
-- name    : UnrelatedSched.FixedMachines.residual_lp_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:01.176284+00:00
-- url     : https://prove2.me/theorems/ccd5f1c3-35a1-42af-81e2-621d4c040417
-- title:
--   §3, p. 6 — a schedule of makespan at most $d$ makes the residual LP feasible
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of positive integer processing times, $d\ge 0$ an integer deadline and $\varepsilon>0$. Let $\sigma$ be a schedule with makespan at most $d$. Let $L$ be its partial schedule of long assignments: $L$ assigns job $j$ to $\sigma(j)$ when $p_{\sigma(j)j}>\varepsilon d$ and leaves $j$ unassigned otherwise, and let $t_i$ be the total processing time of the long assignments to machine $i$. Then
--
--   1. $L$ is an admissible schedule of long assignments ($t_i\le d$ for every $i$), and
--   2. the $0$–$1$ matrix $x$ with $x_{ij}=1$ exactly when job $j$ is unassigned by $L$ and $\sigma(j)=i$ is a feasible solution of the residual linear program: (LP) of the Rounding Theorem for the unassigned jobs, with deadlines $d_i=d-t_i$ and threshold $t=\varepsilon d$.
--
--   In the paper: "If the instance $(P,d)$ has a feasible schedule, then this includes a partial schedule of long assignments … If we then set $t=\varepsilon d$, we see that the linear program (LP) must once again have a feasible solution." This is what makes a 'no' answer of the procedure $A_\varepsilon$ correct.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Section 3, proof of Theorem 3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment

namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

/-- §3, p. 6: if `σ` is a schedule with makespan at most `d`, then its long assignments
(`L j = some (σ j)` exactly when `p_{σ(j) j} > ε d`) form an admissible schedule of long
assignments, and the 0-1 matrix of `σ` on the remaining jobs is a feasible solution of the
residual LP with `d_i = d - t_i` and `t = ε d`. -/
theorem residual_lp_feasible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (σ : Fin n → Fin m)
    (hσ : makespan (fun i j => (P i j : ℝ)) σ ≤ (d : ℝ)) :
    let L : Fin n → Option (Fin m) :=
      fun j => if ε * (d : ℝ) < (P (σ j) j : ℝ) then some (σ j) else none
    IsAdmissible P ε d L ∧
      (fun i j => if L j = none ∧ σ j = i then (1 : ℝ) else 0) ∈ ResidualLP P ε d L := by sorry

end UnrelatedSched.FixedMachines

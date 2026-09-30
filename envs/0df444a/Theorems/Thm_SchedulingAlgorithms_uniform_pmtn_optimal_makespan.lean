-- Prove2me | Theorems.Thm_SchedulingAlgorithms_uniform_pmtn_optimal_makespan
-- name    : SchedulingAlgorithms.uniform_pmtn_optimal_makespan
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:14:35.265522+00:00
-- url     : https://prove2.me/theorems/162ab25f-d7cd-4ec6-9d18-2e0900652b9a
-- title:
--   Theorem 5.8 — the optimal makespan of Q | pmtn | Cmax is the bound w of (5.5)
-- statement:
--   Consider $n$ jobs with positive processing requirements sorted as $p_1\ge p_2\ge\dots\ge p_n$,
--   to be processed preemptively on $m$ uniform machines with positive speeds sorted as
--   $s_1\ge s_2\ge\dots\ge s_m$, where $1\le m\le n$. With $P_j=\sum_{i\le j}p_i$ and
--   $S_j=\sum_{i\le j}s_i$, let
--
--   $$
--   w \;=\; \max\Bigl\{\max_{j=1}^{m-1}\frac{P_j}{S_j},\ \frac{P_n}{S_m}\Bigr\} .
--   $$
--
--   Then there is a feasible preemptive schedule whose makespan equals $w$ and which is optimal:
--   its makespan is at most the makespan of every feasible preemptive schedule. Equivalently, the
--   optimal value of $Q\mid pmtn\mid C_{\max}$ is exactly $w$.
--
--   This is Theorem 5.8 stated as a fact about schedules rather than about the level algorithm:
--   the book proves the theorem by showing that the schedule the level algorithm builds — jobs of
--   highest remaining level always assigned to the fastest free machines, ties processed jointly by
--   time-sharing — finishes at time $w$, and that $w$ is a lower bound (5.5). The result contains
--   McNaughton's rule for identical machines as the case $s_1=\dots=s_m=1$, where $w$ reduces to
--   $\max\{\max_i p_i,\,P_n/m\}$.
--
--   **Formalization Note** The statement asserts the existence of an optimal schedule and pins its
--   value to $w$; it does not assert that the level algorithm produces it, since the algorithm is
--   not part of the statement. Feasibility, makespan and $w$ are as in the definition file. The
--   sorted orders, the positivity of speeds and requirements, and $n\ge m$ are the section's
--   standing assumptions on p. 124; the normalisation $s_1=1$ is not assumed, as the statement is
--   invariant under scaling all speeds.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — Section 5.1.2, printed p. 127 (PDF p. 139), Theorem 5.8: "Algorithm level constructs an optimal schedule for problem Q | pmtn | Cmax", whose proof (pp. 127-128) shows that the schedule constructed has length exactly the lower bound w of (5.5), printed p. 125 (PDF p. 137).

import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_optimal_makespan {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p) :
    ∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S = levelBound s p ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible s p S' → makespan S ≤ makespan S' := by sorry
end SchedulingAlgorithms

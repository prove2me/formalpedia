-- Prove2me | Theorems.Thm_SchedulingAlgorithms_uniform_pmtn_lower_bound
-- name    : SchedulingAlgorithms.uniform_pmtn_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:12:39.933956+00:00
-- url     : https://prove2.me/theorems/9a396845-2762-416b-8607-13060b723ae4
-- title:
--   (5.5) — the bound w is a lower bound for Q | pmtn | Cmax
-- statement:
--   Consider $n$ jobs with positive processing requirements sorted as $p_1\ge p_2\ge\dots\ge p_n$,
--   to be processed preemptively on $m$ uniform machines with positive speeds sorted as
--   $s_1\ge s_2\ge\dots\ge s_m$, where $1\le m\le n$. Let $P_j=\sum_{i\le j}p_i$ and
--   $S_j=\sum_{i\le j}s_i$. Then every feasible preemptive schedule has makespan at least
--
--   $$
--   w \;=\; \max\Bigl\{\max_{j=1}^{m-1}\frac{P_j}{S_j},\ \frac{P_n}{S_m}\Bigr\} .
--   $$
--
--   Here a feasible schedule is a finite list of pieces (job, machine, start, stop) in which no two
--   pieces on one machine overlap, no two pieces of one job overlap, and each job $i$ receives
--   total work $\sum s_{j}\,(\text{stop}-\text{start})=p_i$ over its pieces; the makespan is the
--   largest stop time.
--
--   This is the bound (5.5) of Section 5.1.2. The term $P_n/S_m$ says that all the work has to fit
--   into the total capacity $S_m T$ of the $m$ machines during $[0,T]$. The term $P_j/S_j$ says
--   that the $j$ longest jobs, which can occupy at most $j$ machines at any instant, cannot be
--   processed faster than at the combined rate of the $j$ fastest machines.
--
--   **Formalization Note** The sorted orders are hypotheses, `Antitone p` and `Antitone s`, because
--   the formula names the $j$ *first* jobs and machines. Positivity of the speeds makes every $S_j$
--   with $j\ge 1$ positive, so no division in $w$ is a division by zero; the book's normalisation
--   $s_1=1$ is not assumed, since the bound is invariant under scaling all speeds and the book uses
--   the normalisation only for a running-time estimate. The book's convention that a job is
--   processed by at most one machine at a time is part of feasibility and is exactly what the
--   $P_j/S_j$ terms rely on.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — Section 5.1.2, printed pp. 124-125 (PDF pp. 136-137), the bound (5.5): "w := max{max_{j=1}^{m-1} P_j/S_j, P_n/S_m} (5.5) is a lower bound for the Cmax-values", under the section's standing assumptions 1 = s_1 ≥ s_2 ≥ ... ≥ s_m, p_1 ≥ p_2 ≥ ... ≥ p_n and n ≥ m.

import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_lower_bound {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (S : PreemptiveSchedule n m) (hS : IsFeasible s p S) :
    levelBound s p ≤ makespan S := by sorry
end SchedulingAlgorithms

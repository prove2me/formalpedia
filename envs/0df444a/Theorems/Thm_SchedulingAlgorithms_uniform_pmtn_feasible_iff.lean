-- Prove2me | Theorems.Thm_SchedulingAlgorithms_uniform_pmtn_feasible_iff
-- name    : SchedulingAlgorithms.uniform_pmtn_feasible_iff
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:13:35.697784+00:00
-- url     : https://prove2.me/theorems/829a2c3f-0c67-456b-bdeb-40e24faed67a
-- title:
--   (5.8) — jobs fit into an interval of length T iff sum_{i in A} p_i ≤ T h(A) for every set A
-- statement:
--   Consider $n$ jobs with positive processing requirements sorted as $p_1\ge\dots\ge p_n$ and
--   $m\ge 1$ uniform machines with positive speeds sorted as $s_1\ge\dots\ge s_m$, and a length
--   $T\ge 0$. For a set $A$ of jobs put
--
--   $$
--   h(A)\;=\;\begin{cases}S_{|A|} & \text{if } |A|\le m,\\ S_m & \text{otherwise,}\end{cases}
--   \qquad S_j=\sum_{i\le j}s_i ,
--   $$
--
--   the largest combined speed that $|A|$ jobs can use at one instant. Then the jobs can be
--   scheduled preemptively within the interval $[0,T]$ — some feasible preemptive schedule has
--   makespan at most $T$ — if and only if
--
--   $$
--   \sum_{i\in A}p_i\;\le\;T\,h(A)\qquad\text{for all } A\subseteq\{1,\dots,n\}. \tag{5.8}
--   $$
--
--   This is condition (5.8) of Section 5.1.2, the necessary and sufficient condition the book
--   derives from the level algorithm and then uses in Theorem 5.9 to reduce $Q\mid pmtn; r_i\mid
--   L_{\max}$ to a flow problem. Necessity is the counting argument behind (5.5) applied to an
--   arbitrary set of jobs; sufficiency is that (5.8) for the sets $\{1,\dots,j\}$ says exactly that
--   the bound $w$ of (5.5) is at most $T$, and the level algorithm then finishes by time $w$.
--
--   **Formalization Note** The condition is quantified over all subsets $A$, as printed, including
--   $A=\emptyset$ (where it reads $0\le 0$) and sets with $|A|>m$. Feasibility and makespan are as
--   in the definition file; "within an interval of length $T$" is the requirement that every piece
--   stops by time $T$, which with $T\ge 0$ is the book's meaning. The sorted orders are the
--   section's standing assumptions and are kept, although the displayed condition is symmetric in
--   the jobs. No relation between $n$ and $m$ is assumed, since the book states (5.8) for
--   arbitrary $n$ through the case distinction in $h$.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — Section 5.1.2, printed pp. 128-129 (PDF pp. 140-141), condition (5.8): "jobs 1, ..., n with processing requirements p_1, ..., p_n can be scheduled within an interval of length T if and only if sum_{i in A} p_i ≤ T h(A) for all A ⊆ {1, ..., n}", with h(A) = S_|A| if |A| ≤ m and S_m otherwise, under the section's standing assumptions s_1 ≥ ... ≥ s_m and p_1 ≥ ... ≥ p_n.

import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_feasible_iff {n m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S ≤ T) ↔
      ∀ A : Finset (Fin n), ∑ i ∈ A, p i ≤ T * speedCapacity s A := by sorry
end SchedulingAlgorithms

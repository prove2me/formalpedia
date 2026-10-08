-- Prove2me | Theorems.Thm_SchedSurvey_O2_fig_5_1_blocks_feasible
-- name    : SchedSurvey.O2.fig_5_1_blocks_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:22.599309+00:00
-- url     : https://prove2.me/theorems/a255e982-6b5b-4f35-ab68-a4429b6fbd56
-- title:
--   §5.2.1, p. 312, Fig. 5.1 — the blocks B′ ∪ {J_l} and A′ ∪ {J_r} have feasible staircase schedules without idle time
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, the sets $A = \{J_j \mid a_j \ge b_j\}$ and $B = \{J_j \mid a_j < b_j\}$, and two distinct jobs $J_r$, $J_l$ with $a_r \ge \max_{J_j \in A} b_j$ and $b_l \ge \max_{J_j \in B} a_j$. Let $A' = A - \{J_r, J_l\}$ and $B' = B - \{J_r, J_l\}$, and list the jobs of $B'$ and of $A'$ in an arbitrary order.
--
--   1. **Left block** ($B' \cup \{J_l\}$, Fig. 5.1 left). Run $J_l$ followed by the jobs of $B'$ back to back on $M_1$ from time $0$, and in the same order back to back on $M_2$ from time $a_l$. This is a feasible schedule of $B' \cup \{J_l\}$.
--   2. **Right block** ($A' \cup \{J_r\}$, Fig. 5.1 right). Run the jobs of $A'$ followed by $J_r$ back to back on $M_1$ from time $0$, and in the same order back to back on $M_2$ from time
--   $$
--   \sum_{J_j \in A' \cup \{J_r\}} a_j \;-\; \sum_{J_j \in A' \cup \{J_r\}} b_j \;+\; b_r ,
--   $$
--   so that $M_2$ finishes exactly $b_r$ after $M_1$, $J_r$ starting on $M_2$ when it ends on $M_1$. This is a feasible schedule of $A' \cup \{J_r\}$.
--
--   In both blocks each machine works without idle time from its first to its last job, by construction. These two blocks are the building pieces that the survey combines into a schedule of all jobs.
--
--   **Formalization Note** An order of $B'$ is a duplicate-free list whose members are exactly the jobs of $B$ other than $J_r, J_l$ (likewise for $A'$). Start times are given by `contigStart`; feasibility is `IsFeasibleOn` the block's job set. The figure shows each block up to translation in time; here each block's $M_1$ starts at time $0$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "We assert that it is possible to form feasible schedules for B′ ∪ {J_l} and for A′ ∪ {J_r} as indicated in Fig. 5.1 …", Fig. 5.1

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312, Fig. 5.1: for distinct `r`, `l` chosen as on p. 312 and any orderings `LB` of
`B' = B − {J_r, J_l}` and `LA` of `A' = A − {J_r, J_l}`, the two staircase blocks are feasible
schedules of their job sets:
* left block, jobs `l :: LB`: on `M₁` back to back from time `0`; on `M₂` back to back from
  time `a_l`;
* right block, jobs `LA ++ [r]`: on `M₁` back to back from time `0`; on `M₂` back to back from
  time `Σ_{LA ++ [r]} a − Σ_{LA ++ [r]} b + b_r`, so that `M₂` ends `b_r` after `M₁`.
Both machines run without idle time inside each block by construction (`contigStart`). -/
theorem fig_5_1_blocks_feasible {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (r l : Fin n) (hrl : r ≠ l)
    (hr : ∀ j ∈ setA a b, b j ≤ a r) (hl : ∀ j ∈ setB a b, a j ≤ b l)
    (LA LB : List (Fin n)) (hLA : LA.Nodup) (hLB : LB.Nodup)
    (hLAmem : ∀ j, j ∈ LA ↔ (j ∈ setA a b ∧ j ≠ r ∧ j ≠ l))
    (hLBmem : ∀ j, j ∈ LB ↔ (j ∈ setB a b ∧ j ≠ r ∧ j ≠ l)) :
    IsFeasibleOn (l :: LB).toFinset a b
        ⟨contigStart a (l :: LB), fun j => a l + contigStart b (l :: LB) j⟩ ∧
      IsFeasibleOn (LA ++ [r]).toFinset a b
        ⟨contigStart a (LA ++ [r]),
          fun j => ((LA ++ [r]).map a).sum - ((LA ++ [r]).map b).sum + b r
            + contigStart b (LA ++ [r]) j⟩ := by sorry

end SchedSurvey.O2

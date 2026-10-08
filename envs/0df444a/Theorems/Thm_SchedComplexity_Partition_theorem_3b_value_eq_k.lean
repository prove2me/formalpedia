-- Prove2me | Theorems.Thm_SchedComplexity_Partition_theorem_3b_value_eq_k
-- name    : SchedComplexity.Partition.theorem_3b_value_eq_k
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T22:02:34.929153+00:00
-- url     : https://prove2.me/theorems/558ee85b-d806-4912-bdb4-2588ef54ae6e
-- title:
--   Proof of Theorem 3(b) — with $p_j=w_j$, $\sum w_jC_j=k(S)$ for every order
-- statement:
--   In construction (b) of Theorem 3 ($n=t$ jobs, $p_{j1}=w_j=a_j$, two identical machines), let $S$ be the set of jobs assigned to $M_1$, so that $T-S$ is assigned to $M_2$. Then:
--
--   1. for every schedule with this assignment in which each machine processes its jobs without idle time from time $0$, in any order,
--   $$\sum_j w_jC_j = k(S);$$
--   2. every feasible schedule with this assignment has $\sum_j w_jC_j \ge k(S)$.
--
--   Part 1 is the paper's statement that "the value of $\sum w_jC_j$ is not influenced by the ordering of the jobs on the machines and only depends on the choice of $S$". Part 2 makes explicit what this sentence needs in the recognition problem, where schedules may contain idle time: inserting idle time never lowers the value.
--
--   **Formalization Note** The statement holds for all natural data $a_j$, so positivity is not assumed. Machine $M_1$ is machine `0`.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, proof of Theorem 3(b)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Proof of Theorem 3(b) (p. 15): in construction (b) (`p_{j1} = w_j = a_j`), let `S` be the set
of jobs assigned to `M_1` (machine `0`) and `T − S` those on `M_2`. If each machine works without
idle time from `0`, then `Σ w_j C_j = k(S)` whatever the order of the jobs; every feasible
schedule with this assignment has `Σ w_j C_j ≥ k(S)`. -/
theorem theorem_3b_value_eq_k (a : List ℕ) (S : Finset (Fin a.length))
    (σ : Schedule a.length) (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) :
    (σ.IsNonIdle (procB a) → σ.sumWC (procB a) (procB a) = kVal a S) ∧
      (σ.IsFeasible (procB a) → kVal a S ≤ σ.sumWC (procB a) (procB a)) := by sorry

end SchedComplexity.Partition

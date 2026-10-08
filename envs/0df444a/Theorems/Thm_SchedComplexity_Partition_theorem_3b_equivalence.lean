-- Prove2me | Theorems.Thm_SchedComplexity_Partition_theorem_3b_equivalence
-- name    : SchedComplexity.Partition.theorem_3b_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:07.552049+00:00
-- url     : https://prove2.me/theorems/c926acf5-e8a3-46cd-a354-b249590ac959
-- title:
--   Theorem 3(b) — PARTITION solvable iff $\sum w_jC_j\le y$ with $p_j=w_j=a_j$
-- statement:
--   Let $a_1,\dots,a_t$ be positive integers and $A=\sum_{j\in T}a_j$. Consider the instance of $n|2|I|\sum w_jC_j$ with $n=t$ jobs, $p_{j1}=w_j=a_j$, and the threshold
--
--   $$y=\sum_{j,k\in T,\ j\le k}a_ja_k-\tfrac14A^2 .$$
--
--   Then PARTITION has a solution for $a_1,\dots,a_t$ if and only if this instance has a feasible schedule with $\sum_j w_jC_j\le y$.
--
--   This is the yes-instance equivalence behind the reduction PARTITION $\propto n|2|I|\sum w_jC_j$ of Theorem 3(b).
--
--   **Formalization Note** The threshold is compared as a real number, exactly as printed; it is not an integer when $A$ is odd.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, Theorem 3(b) and its proof

import Mathlib
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Theorem 3(b) (p. 15): for positive integers `a_1, …, a_t`, PARTITION has a solution iff the
two-identical-machine instance `n = t`, `p_{j1} = w_j = a_j` has a feasible schedule with
`Σ w_j C_j ≤ y = Σ_{j,k∈T, j≤k} a_j a_k − ¼A²`. -/
theorem theorem_3b_equivalence (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
        (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a := by sorry

end SchedComplexity.Partition

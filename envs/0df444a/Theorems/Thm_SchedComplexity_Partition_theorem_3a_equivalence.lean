-- Prove2me | Theorems.Thm_SchedComplexity_Partition_theorem_3a_equivalence
-- name    : SchedComplexity.Partition.theorem_3a_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T22:02:23.232379+00:00
-- url     : https://prove2.me/theorems/c43cfb97-9486-4ce0-9ea9-6e802cc4e50f
-- title:
--   Theorem 3(a) — PARTITION solvable iff $C_{\max}\le \tfrac12A$ on two identical machines
-- statement:
--   Let $a_1,\dots,a_t$ be positive integers and $A=\sum_{j\in T}a_j$. Consider the instance of $n|2|I|C_{\max}$ with $n=t$ jobs and processing times $p_{j1}=a_j$. Then
--
--   $$\exists\, S\subseteq T:\ \sum_{j\in S}a_j=\sum_{j\in T-S}a_j \iff \exists\text{ a feasible schedule with } C_j\le \tfrac12 A \text{ for all } j.$$
--
--   This is the yes-instance equivalence behind the reduction PARTITION $\propto n|2|I|C_{\max}$ of Theorem 3(a). The paper prints only the construction and states on p. 14 that such equivalences are "trivial or clear" where not proved.
--
--   **Formalization Note** The threshold $\tfrac12A$ is compared as a real number, exactly as printed; schedules have natural-number starting times (see the model definition).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, Theorem 3(a) with p. 14 (the equivalence form of the reductions)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Theorem 3(a) (p. 15): for positive integers `a_1, …, a_t`, PARTITION has a solution iff the
two-identical-machine instance `n = t`, `p_{j1} = a_j` has a feasible schedule with
`C_max ≤ y = ½A`. -/
theorem theorem_3a_equivalence (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
        ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a := by sorry

end SchedComplexity.Partition

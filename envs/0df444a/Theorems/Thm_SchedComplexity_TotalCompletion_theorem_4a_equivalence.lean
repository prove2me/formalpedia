-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_theorem_4a_equivalence
-- name    : SchedComplexity.TotalCompletion.theorem_4a_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:59.336407+00:00
-- url     : https://prove2.me/theorems/427e8640-e346-4d1b-b78f-48fb3aa1b120
-- title:
--   Theorem 4(a), equivalence: KNAPSACK has a solution iff the constructed instance has $\sum_jC_j\le y$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Let the instance with $n=t+t'+u+1$ jobs and the threshold $y$ be those of the construction of Theorem 4(a). Then
--
--   $$\exists S\subseteq T:\ \sum_{j\in S}a_j=b \quad\Longleftrightarrow\quad \text{the instance is in } n|1|r_n\ge0,w_j=1|\textstyle\sum w_jC_j \text{ and has a feasible schedule with } \sum_jC_j\le y .$$
--
--   This is the correctness of the reduction in Theorem 4(a); the proof combines the forward direction with claims (A)–(D).
--
--   **Formalization Note** The paper ends the converse with "This implies that KNAPSACK has a solution, as is easily seen"; the Lean statement asserts the full equivalence. The hypothesis $0<b<A$ is the paper's "We may assume that $0<b<A$" (p. 16). Class membership of the constructed instance (unit weights, release date $0$ for every job but $J_n$) is part of the right-hand side. Starting times are natural numbers.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 22–23, proof of Theorem 4(a); p. 16 (0 < b < A)

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Theorem 4(a), the equivalence of the reduction (pp. 22–23): for positive integers
`a_1, …, a_t, b` with `0 < b < A`, KNAPSACK has a solution if and only if the constructed
instance belongs to the class `n|1|r_n≥0,w_j=1|Σw_jC_j` and has a feasible schedule with
`Σ_j C_j ≤ y`. -/
theorem theorem_4a_equivalence {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a) :
    SchedComplexity.Tardiness.KnapsackYes a b ↔
      IsYes (procTime a b) (weight a b) (release a b) (yThreshold a b) := by sorry

end SchedComplexity.TotalCompletion

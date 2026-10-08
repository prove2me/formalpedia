-- Prove2me | Theorems.Thm_SchedComplexity_Shops_theorem_4j_equivalence
-- name    : SchedComplexity.Shops.theorem_4j_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:27.875871+00:00
-- url     : https://prove2.me/theorems/a0d432a7-afde-439e-aa8f-843b4d295089
-- title:
--   Theorem 4(j) — KNAPSACK has a solution iff the three-machine job shop instance has C_max ≤ 2A
-- statement:
--   Let $a_1,\dots,a_t$ and $b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Consider the three-machine job shop with $n=t+2$ jobs: item job $J_j$ ($j\in T$) has machine order $(M_1,M_3)$ and processing times $a_j,a_j$; $J_{n-1}$ has order $(M_1,M_2)$ and times $b$, $2(A-b)$; $J_n$ has order $(M_2,M_3)$ and times $2b$, $A-b$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad\text{the instance has a feasible schedule with } C_{\max}\le 2A.$$
--
--   This is the equivalence in the proof of Theorem 4(j), which shows that KNAPSACK reduces to $n|3|G,m_j{\le}2|C_{\max}$.
--
--   **Formalization Note** The assumption $0<b<A$ and the positivity of the data are hypotheses. The equivalence is stated with "value $\le y$" (p. 14).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 17, proof of Theorem 4(j)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(j), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the three-machine job
shop `constrJ a b` (items with order `(M_1, M_3)` and times `a_j, a_j`; `J_{n-1}` with order
`(M_1, M_2)` and times `b, 2(A - b)`; `J_n` with order `(M_2, M_3)` and times `2b, A - b`) has a
feasible schedule with `C_max ≤ y = 2A`. -/
theorem theorem_4j_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrJ a b).HasScheduleLE (yJ a) := by sorry

end SchedComplexity.Shops

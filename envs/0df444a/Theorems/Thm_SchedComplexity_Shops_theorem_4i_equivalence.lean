-- Prove2me | Theorems.Thm_SchedComplexity_Shops_theorem_4i_equivalence
-- name    : SchedComplexity.Shops.theorem_4i_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:23.171519+00:00
-- url     : https://prove2.me/theorems/b3b09e2a-d986-4872-86e2-ede433fd607d
-- title:
--   Theorem 4(i) — KNAPSACK has a solution iff the two-machine job shop instance has C_max ≤ A + 1
-- statement:
--   Let $a_1,\dots,a_t$ and $b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Consider the two-machine job shop with $n=t+1$ jobs in which item job $J_j$ ($j\in T$) has the single operation $p_{j1}=a_j$ on $M_1$, and $J_n$ has machine order $(M_2,M_1,M_2)$ with processing times $b$, $1$, $A-b$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad\text{the instance has a feasible schedule with } C_{\max}\le A+1.$$
--
--   This is the equivalence in the proof of Theorem 4(i), which shows that KNAPSACK reduces to $n|2|G,m_j{\le}3|C_{\max}$.
--
--   **Formalization Note** The report writes "we may assume that $0<b<A$"; the theorem carries this, and the positivity of the data, as hypotheses. The report proves the forward direction with a schedule of value exactly $y$; the equivalence it concludes is with "value $\le y$", which is what is stated.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16, proof of Theorem 4(i)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(i), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 16: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine job shop
`constrI a b` (items on `M_1` with `p_j1 = a_j`; `J_n` with machine order `(M_2, M_1, M_2)` and
times `b, 1, A - b`) has a feasible schedule with `C_max ≤ y = A + 1`. -/
theorem theorem_4i_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrI a b).HasScheduleLE (yI a) := by sorry

end SchedComplexity.Shops

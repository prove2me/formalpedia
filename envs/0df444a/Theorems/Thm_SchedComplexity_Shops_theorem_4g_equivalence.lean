-- Prove2me | Theorems.Thm_SchedComplexity_Shops_theorem_4g_equivalence
-- name    : SchedComplexity.Shops.theorem_4g_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:39.164907+00:00
-- url     : https://prove2.me/theorems/1fd5a535-9cd8-4923-bb35-eef84d429eca
-- title:
--   Theorem 4(g) — KNAPSACK has a solution iff the flow shop with release date r_n = tb has C_max ≤ t(A + 1)
-- statement:
--   Let $a_1,\dots,a_t$ and $b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Consider the two-machine flow shop (every job visits $M_1$, then $M_2$) with $n=t+1$ jobs: item job $J_j$ ($j\in T$) has release date $0$ and processing times $p_{j1}=ta_j$, $p_{j2}=1$; $J_n$ has release date $r_n=tb$ and processing times $p_{n1}=1$, $p_{n2}=t(A-b)$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad\text{the instance has a feasible schedule with } C_{\max}\le t(A+1).$$
--
--   This is the equivalence in the proof of Theorem 4(g), which shows that KNAPSACK reduces to $n|2|F,r_n{\ge}0|C_{\max}$.
--
--   **Formalization Note** The report prints the two directions and leaves the concluding "if and only if" implicit, as in reductions (i) and (j); the theorem states it. The assumption $0<b<A$ and the positivity of the data are hypotheses.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 18, proof of Theorem 4(g)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(g), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 18: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine flow shop
`constrG a b` (items with `r_j = 0`, `p_j1 = t a_j`, `p_j2 = 1`; `J_n` with `r_n = t b`,
`p_n1 = 1`, `p_n2 = t(A - b)`) has a feasible schedule with `C_max ≤ y = t(A + 1)`. -/
theorem theorem_4g_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrG a b).HasScheduleLE (yG a) := by sorry

end SchedComplexity.Shops

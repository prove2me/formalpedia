-- Prove2me | Theorems.Thm_SchedComplexity_Shops_theorem_4h_equivalence
-- name    : SchedComplexity.Shops.theorem_4h_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:34.970976+00:00
-- url     : https://prove2.me/theorems/dcc17e55-a543-493f-9018-669e1034585a
-- title:
--   Theorem 4(h) — KNAPSACK has a solution iff the flow shop with J_{n−1} < J_n has C_max ≤ t(A + 1) + 1
-- statement:
--   Let $a_1,\dots,a_t$ and $b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Consider the two-machine flow shop with $n=t+2$ jobs, all released at time $0$: item job $J_j$ ($j\in T$) has processing times $p_{j1}=ta_j$, $p_{j2}=1$; $J_{n-1}$ has $p_{n-1,1}=1$, $p_{n-1,2}=tb$; $J_n$ has $p_{n1}=1$, $p_{n2}=t(A-b)$; and the only precedence constraint is $J_{n-1}<J_n$, i.e. $C_{n-1}\le B_n$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad\text{the instance has a feasible schedule with } C_{\max}\le t(A+1)+1.$$
--
--   This is the equivalence in the proof of Theorem 4(h), which shows that KNAPSACK reduces to $n|2|F,\mathit{tree}|C_{\max}$.
--
--   **Formalization Note** The report proves only the bound "$R\ne\emptyset\Rightarrow C_{\max}\ge t(A+1)+2>y$" and says that "the remainder of the equivalence proof is analogous to that of reduction (g)"; the theorem states the full equivalence that this remark asserts. The assumption $0<b<A$ and the positivity of the data are hypotheses (the bound above uses $p_{j1}=ta_j\ge t$).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 18, proof of Theorem 4(h)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(h), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 18: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine flow shop
`constrH a b` (items with `p_j1 = t a_j`, `p_j2 = 1`; `J_{n-1}` with `p = (1, t b)`; `J_n` with
`p = (1, t(A - b))`; precedence `J_{n-1} < J_n`) has a feasible schedule with
`C_max ≤ y = t(A + 1) + 1`. -/
theorem theorem_4h_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrH a b).HasScheduleLE (yH a) := by sorry

end SchedComplexity.Shops

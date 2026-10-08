-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_theorem_4c_equivalence
-- name    : SchedComplexity.OneMachine.theorem_4c_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:51:17.051349+00:00
-- url     : https://prove2.me/theorems/47535cea-8d28-4fdc-b849-469cd342a7d7
-- title:
--   Theorem 4(c) — KNAPSACK has a solution iff the constructed $n|1|r_n\ge0|L_{\max}$ instance has $L_{\max}\le0$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, where $A=\sum_{j\in T}a_j$. Consider the single-machine instance of reduction (c): $n=t+1$ jobs, the jobs $j\in T$ released at $0$ with $p_{j1}=a_j$ and $d_j=A+1$, and the last job released at $r_n=b$ with $p_{n1}=1$ and $d_n=b+1$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad \exists\text{ feasible schedule with } L_j=C_j-d_j\le 0\ \text{for all } j .$$
--
--   This is the yes-instance equivalence behind the reduction KNAPSACK $\propto n|1|r_n\ge0|L_{\max}$ (threshold $y=0$); the paper refers to reduction (i) and to Figure 4, where $S$ is processed in $[0,b]$, $J_n$ in $[b,b+1]$ and $T-S$ in $[b+1,A+1]$.
--
--   **Formalization Note** The hypotheses $0<b<A$ are the proof's "We may assume that $0<b<A$" (p. 16); without $b\le A$ the equivalence fails (for $b>A$ every job meets its due date while KNAPSACK has no solution), so the goal's reduction must treat such inputs separately. Schedules may contain idle time; the paper writes only "Cf. reduction (i) and Figure 4", and the statement makes the equivalence explicit for all feasible schedules.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 17, Theorem 4(c)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(c), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j` (the proof's standing assumption,
p. 16), KNAPSACK has a solution iff the constructed `n|1|r_n≥0|L_max` instance has a feasible
schedule with `L_max ≤ y = 0`, i.e. `C_j - d_j ≤ 0` for every job. -/
theorem theorem_4c_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0 := by sorry

end SchedComplexity.OneMachine
